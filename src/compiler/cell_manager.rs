use std::{collections::HashMap, rc::Rc};

use crate::ast::{Circuit, ForwardSignal, InternalSignal, StepType};

use super::{Column, CompilationUnit};

#[derive(Clone, Debug)]
pub struct SignalPlacement {
    pub column: Column,
    pub rotation: i32,
}

#[derive(Debug, Clone)]
pub struct StepPlacement {
    height: u32,
    signals: HashMap<InternalSignal, SignalPlacement>, // internal signals are attached to a step
}

#[derive(Debug, Clone)]
pub struct Placement<F, StepArgs> {
    pub forward: HashMap<ForwardSignal, SignalPlacement>, // forward signals aren't tied to a step
    pub steps: HashMap<Rc<StepType<F, StepArgs>>, StepPlacement>, // stepplacement contain internal signal splacement
    pub columns: Vec<Column>,
}

impl<F, StepArgs> Default for Placement<F, StepArgs> {
    fn default() -> Self {
        Self {
            forward: Default::default(),
            steps: Default::default(),
            columns: Default::default(),
        }
    }
}

impl<F, StepArgs> Placement<F, StepArgs> { // can directly find the sigal
    pub fn get_forward_placement(&self, forward: &ForwardSignal) -> SignalPlacement {
        self.forward
            .get(forward)
            .expect("forward signal not found")
            .clone()
    }

    pub fn find_internal_signal_placement( // need to find the step where the signal is defined in first, as the placement is stored in a nested hashmap 
        &self,
        step: &StepType<F, StepArgs>,
        signal: &InternalSignal,
    ) -> SignalPlacement {
        self.steps
            .get(step)
            .expect("step not found")
            .signals
            .get(signal)
            .expect("signal not found")
            .clone()
    }

    pub fn step_height(&self, step: &StepType<F, StepArgs>) -> u32 {
        self.steps.get(step).expect("step not found").height
    }
}

pub trait CellManager {
    fn place<F, TraceArgs, StepArgs>(
        &self,
        unit: &mut CompilationUnit<F, StepArgs>,
        sc: &Circuit<F, TraceArgs, StepArgs>, // circuit defined in ast
    );
}

#[derive(Debug, Default)]
pub struct SingleRowCellManager {} // 

impl CellManager for SingleRowCellManager {
    fn place<F, TraceArgs, StepArgs>( // converts ast Circuit object and its forward/internal signals to the CompilationUnit object's placement field
        &self,
        unit: &mut CompilationUnit<F, StepArgs>, // compiler CompilationUnit
        sc: &Circuit<F, TraceArgs, StepArgs>, // ast Circuit
    ) {
        let mut placement = Placement::<F, StepArgs> {
            forward: HashMap::new(),
            steps: HashMap::new(),
            columns: Vec::new(),
        };

        let mut forward_signals: u32 = 0;

        for forward_signal in sc.forward_signals.iter() { // loop over all forward signal in the ast Circuit, creating a column for each
            let column = if let Some(annotation) = unit.annotations.get(&forward_signal.uuid()) { // if annotation hashmap has the uuid of the forward signal
                Column::advice( // create advice column with annotation and phase
                    format!("srcm forward {}", annotation), // ??? what does srcm forward mean
                    forward_signal.phase(),
                )
            } else {
                Column::advice("srcm forward", forward_signal.phase())
            };
            // looks like Placement's column field stores actual Column objects and forward field stores both the column counter and the actual Column object
            placement.columns.push(column.clone()); 

            placement.forward.insert(
                *forward_signal, // the actual signal, with id and annotation
                SignalPlacement {
                    column, // the actual Column object
                    rotation: 0,
                },
            );

            forward_signals += 1; // counter u32
        }

        let mut max_internal_width: u32 = 0;
        // each outer loop inserts a StepType -> StepPlacement KV pair to the steps field of Placement
        // each inner loop inserts a InternalSignal -> SignalPlacement KV pair to the StepPlacement HashMap
        for step in unit.step_types.values() { // values are StepType values in the step_type HashMap field of compiler's Compilation Unit
            let mut internal_signals: u32 = 0; // counter

            let mut step_placement = StepPlacement { // StepPlacement contains internal signals
                height: 1, // This cellmanager always have SuperRows with height 1
                signals: HashMap::new(), // internal signals -> their placements (KV pair)
            };

            for signal in step.signals.iter() { // signal field of step (StepType), which is a Vec<InternalSignal>, looping over each InternalSignal element
                let column_pos = forward_signals + internal_signals; // add two counters
                let column = if placement.columns.len() <= column_pos as usize { // ??? why is this check needed?
                    let column = if let Some(annotation) = unit.annotations.get(&signal.uuid()) { // check if the signal uuid is stored in the annotation HashMap of CompilationUnit annotation
                        Column::advice(format!("srcm internal signal {}", annotation), 0) 
                    } else {
                        Column::advice("srcm internal signal", 0)
                    };

                    placement.columns.push(column.clone()); // push the new Column object to the placement stack
                    column // returns the column for later use
                } else {
                    placement.columns[column_pos as usize].clone() // push to the column_pos index (basically an empty column), if the number of columns in placement object is greater than column_pos
                };

                step_placement.signals.insert( // KV pair of internal signal -> their placement
                    *signal,
                    SignalPlacement {
                        column,
                        rotation: 0,
                    },
                );

                internal_signals += 1; // counter
            }

            placement.steps.insert(Rc::clone(step), step_placement); // steps field of Placement object is KV pair of StepType -> StepPlacement
            max_internal_width = max_internal_width.max(internal_signals); // count of maximum number of internal signals across different step types
        }
        // update the columns and placement fields of CompilationUnit in compiler; columns include forward and internal columns; placement is a giant data structure defined at the top
        unit.columns.extend_from_slice(&placement.columns);
        unit.placement = placement;
    }
}
