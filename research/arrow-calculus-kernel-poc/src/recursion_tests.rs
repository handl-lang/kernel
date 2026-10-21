// Arrow Calculus Recursion Experiments
// Tests for Challenge #5: Recursion via Feedback

// Simplified Value/Arrow types for this experiment
#[derive(Debug, Clone, PartialEq)]
pub enum SimpleValue {
    Int(i32),
    Bool(bool),
    Unit,
    Product(Box<SimpleValue>, Box<SimpleValue>),
}

impl std::fmt::Display for SimpleValue {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SimpleValue::Int(n) => write!(f, "{}", n),
            SimpleValue::Bool(b) => write!(f, "{}", b),
            SimpleValue::Unit => write!(f, "()"),
            SimpleValue::Product(a, b) => write!(f, "({}, {})", a, b),
        }
    }
}

pub fn factorial_step(state: SimpleValue) -> SimpleValue {
    // State: (result, (n, (acc, terminated)))
    // Returns: (result', (n', (acc', terminated')))
    match state {
        SimpleValue::Product(result_box, state_box) => {
            match (*result_box, *state_box) {
                (SimpleValue::Int(result), SimpleValue::Product(n_box, acc_state_box)) => {
                    match (*n_box, *acc_state_box) {
                        (SimpleValue::Int(n), SimpleValue::Product(acc_box, term_box)) => {
                            match (*acc_box, *term_box) {
                                (SimpleValue::Int(acc), SimpleValue::Bool(terminated)) => {
                                    if terminated {
                                        // Keep state unchanged for termination
                                        SimpleValue::Product(
                                            Box::new(SimpleValue::Int(result)),
                                            Box::new(SimpleValue::Product(
                                                Box::new(SimpleValue::Int(n)),
                                                Box::new(SimpleValue::Product(
                                                    Box::new(SimpleValue::Int(acc)),
                                                    Box::new(SimpleValue::Bool(true)),
                                                )),
                                            )),
                                        )
                                    } else if n <= 1 {
                                        // Terminate: set terminated flag, keep result = acc
                                        SimpleValue::Product(
                                            Box::new(SimpleValue::Int(acc)),
                                            Box::new(SimpleValue::Product(
                                                Box::new(SimpleValue::Int(n)),
                                                Box::new(SimpleValue::Product(
                                                    Box::new(SimpleValue::Int(acc)),
                                                    Box::new(SimpleValue::Bool(true)),
                                                )),
                                            )),
                                        )
                                    } else {
                                        // Continue: multiply acc by n, decrement n
                                        let new_acc = acc * n;
                                        SimpleValue::Product(
                                            Box::new(SimpleValue::Int(new_acc)),
                                            Box::new(SimpleValue::Product(
                                                Box::new(SimpleValue::Int(n - 1)),
                                                Box::new(SimpleValue::Product(
                                                    Box::new(SimpleValue::Int(new_acc)),
                                                    Box::new(SimpleValue::Bool(false)),
                                                )),
                                            )),
                                        )
                                    }
                                }
                                _ => SimpleValue::Unit,
                            }
                        }
                        _ => SimpleValue::Unit,
                    }
                }
                _ => SimpleValue::Unit,
            }
        }
        _ => SimpleValue::Unit,
    }
}

pub fn fibonacci_step(input: SimpleValue) -> SimpleValue {
    // Input: (n, (a, b, terminated))
    // Output: (fib_n, (n, (a, b, terminated)))
    match input {
        SimpleValue::Product(n_box, state_box) => {
            match (*n_box, *state_box) {
                (SimpleValue::Int(_n), _state) => {
                    // For Fibonacci, we need to extract (a, b, terminated) from state
                    // This is getting complex with nested Products; for now use simpler approach
                    SimpleValue::Unit
                }
                _ => SimpleValue::Unit,
            }
        }
        _ => SimpleValue::Unit,
    }
}

/// State machine loop:
/// Given a step function s : state -> state, applies it repeatedly until state converges
/// The step function extracts a termination flag from the state
pub fn state_loop(step_fn: fn(SimpleValue) -> SimpleValue, initial_state: SimpleValue, max_iters: usize) -> SimpleValue {
    let mut state = initial_state;
    let mut iterations = max_iters;
    let mut iter_count = 0;
    
    println!("  [loop] initial_state={}", state);
    
    while iterations > 0 {
        iterations -= 1;
        iter_count += 1;
        
        // Run step
        let new_state = step_fn(state.clone());
        
        println!("    [iter {}] {} => {}", iter_count, state, new_state);
        
        // Check for termination: if state is unchanged, we're done
        if new_state == state {
            println!("  [loop] Terminated with state={}", state);
            return state;
        }
        state = new_state;
    }
    
    println!("  [loop] Max iterations exceeded");
    state
}

pub fn extract_result_from_state(state: SimpleValue) -> SimpleValue {
    // State is (result, more_state)
    match state {
        SimpleValue::Product(result, _) => *result,
        _ => SimpleValue::Unit,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factorial_via_loop() {
        // Compute factorial(5) via feedback loop
        // State: (result, (n, (acc, terminated)))
        let initial_state = SimpleValue::Product(
            Box::new(SimpleValue::Int(1)),  // result = 1 initially
            Box::new(SimpleValue::Product(
                Box::new(SimpleValue::Int(5)),  // n = 5
                Box::new(SimpleValue::Product(
                    Box::new(SimpleValue::Int(1)),  // acc = 1
                    Box::new(SimpleValue::Bool(false)),  // terminated = false
                )),
            )),
        );
        
        let final_state = state_loop(factorial_step, initial_state, 100);
        let result = extract_result_from_state(final_state);
        
        assert_eq!(result, SimpleValue::Int(120), "factorial(5) should be 120");
    }

    #[test]
    fn test_factorial_small_values() {
        // Test factorial(0), (1), (2), (3), (4)
        for n in 0..=4 {
            let initial_state = SimpleValue::Product(
                Box::new(SimpleValue::Int(1)),
                Box::new(SimpleValue::Product(
                    Box::new(SimpleValue::Int(n)),
                    Box::new(SimpleValue::Product(
                        Box::new(SimpleValue::Int(1)),
                        Box::new(SimpleValue::Bool(false)),
                    )),
                )),
            );
            
            let final_state = state_loop(factorial_step, initial_state, 100);
            let result = extract_result_from_state(final_state);
            
            let expected = match n {
                0 => 1,
                1 => 1,
                2 => 2,
                3 => 6,
                4 => 24,
                _ => 0,
            };
            
            assert_eq!(
                result,
                SimpleValue::Int(expected),
                "factorial({}) should be {}",
                n,
                expected
            );
        }
    }
}

fn main() {
    println!("Arrow Calculus: Recursion via Feedback Experiments");
    println!("===================================================\n");
    
    // Test 1: Factorial
    println!("Test 1: Factorial(5)");
    let initial_state = SimpleValue::Product(
        Box::new(SimpleValue::Int(1)),
        Box::new(SimpleValue::Product(
            Box::new(SimpleValue::Int(5)),
            Box::new(SimpleValue::Product(
                Box::new(SimpleValue::Int(1)),
                Box::new(SimpleValue::Bool(false)),
            )),
        )),
    );
    let final_state = state_loop(factorial_step, initial_state, 100);
    let result = extract_result_from_state(final_state);
    println!("  Result: {} (expected 120)\n", result);
    
    // Test 2: Factorial sequence
    println!("Test 2: Factorial sequence (0 through 7)");
    for n in 0..=7 {
        let initial_state = SimpleValue::Product(
            Box::new(SimpleValue::Int(1)),
            Box::new(SimpleValue::Product(
                Box::new(SimpleValue::Int(n)),
                Box::new(SimpleValue::Product(
                    Box::new(SimpleValue::Int(1)),
                    Box::new(SimpleValue::Bool(false)),
                )),
            )),
        );
        let final_state = state_loop(factorial_step, initial_state, 100);
        let result = extract_result_from_state(final_state);
        println!("  factorial({}) = {}", n, result);
    }
}
