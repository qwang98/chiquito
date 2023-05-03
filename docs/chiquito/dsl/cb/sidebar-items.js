window.SIDEBAR_ITEMS = {"fn":[["and","The `and` function takes an iterator of input constraints and returns a new constraint representing the logical AND of all input constraints. In practice, multiplies all input constraints together, i.e. A * B * C * … = 0."],["annotate","The `annotate` function takes a string annotation and an expression, and returns a new constraint with the given annotation and expression."],["eq","The `eq` function takes two constraints and returns a new constraint representing the equality of the input constraints."],["if_next_step","The `if_next_step` function takes a `StepTypeHandler` and a constraint, and returns a new constraint that is only applied if the next step is of the given step type."],["isz","The `isz` function takes a constraint and returns a new constraint representing whether the input constraint is zero."],["lookup","Creates a new empty `LookupBuilder` object and returns it. Can chain `**add**` and `**enable**` function calls to build the lookup table."],["next_step_must_be","The `next_step_must_be` function takes a `StepTypeHandler` and returns a new constraint that requires the next step to be of the given step type."],["next_step_must_not_be","The `next_step_must_not_be` function takes a `StepTypeHandler` and returns a new constraint that requires the next step to not be of the given step type."],["not","The `not` function takes a constraint and returns a new constraint representing the logical NOT of the input constraint. The input constraint must have a value of either 0 or 1."],["or","The `or` function takes an iterator of input constraints and returns a new constraint representing the logical OR of all input constraints. In practice, constructs the output constraint in the format of not(and(not(A), not(B), not(C), …)) = 0, which is equivalent to or(A, B, C, …)."],["rlc","The `rlc` function computes the randomized linear combination of the given expressions and randomness."],["select","The `select` function takes a selector constraint and two other constraints, and returns a new constraint that represents the value of `when_true` if the selector is true, or `when_false` if the selector is false."],["unless","The `unless` function takes a selector constraint and a `when_false` constraint, and returns a new constraint that represents the value of `when_false` unless the selector is true, in which case it returns zero."],["when","The `when` function takes a selector constraint and a `when_true` constraint, and returns a new constraint that represents the value of `when_true` if the selector is true, or zero if the selector is false."],["xor","The `xor` function takes two expressions and returns a new expression representing the logical XOR of the input expressions."]],"struct":[["Constraint","The `Constraint` struct represents a constraint with an associated annotation and expression."],["LookupBuilder","The `LookupBuilder` struct is a helper struct for building lookup tables."]]};