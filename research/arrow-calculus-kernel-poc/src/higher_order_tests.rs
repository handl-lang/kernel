// Challenge #2: Abstraction via Higher-Order Arrows
// Tests for parametric arrow constructs and dynamic application
//
// Key questions:
// 1. Can we express parametricity without lambda?
// 2. Can arrows be applied dynamically (like functions)?
// 3. Can higher-order patterns (map, filter, compose) be expressed via arrows?

// Simplified Value type for testing
#[derive(Debug, Clone, PartialEq)]
pub enum SimpleValue {
    Int(i32),
    Bool(bool),
    Unit,
    Product(Box<SimpleValue>, Box<SimpleValue>),
    Left(Box<SimpleValue>),
    Right(Box<SimpleValue>),
    List(Vec<SimpleValue>),
}

impl std::fmt::Display for SimpleValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SimpleValue::Int(n) => write!(f, "{}", n),
            SimpleValue::Bool(b) => write!(f, "{}", b),
            SimpleValue::Unit => write!(f, "()"),
            SimpleValue::Product(a, b) => write!(f, "({}, {})", a, b),
            SimpleValue::Left(v) => write!(f, "Left({})", v),
            SimpleValue::Right(v) => write!(f, "Right({})", v),
            SimpleValue::List(items) => {
                write!(f, "[")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
        }
    }
}

// ============================================================================
// Experiment 1: Higher-Order Arrow - ApplyTwice
// ============================================================================
// Test: Can we express "apply arrow f twice" without lambda?
// Pattern: applyTwice f x = f(f(x))
// Arrow version: applyTwice :: (a ~> a) -> a ~> a
//                applyTwice f = f >>> f

pub fn apply_twice_step(arrow_fn: fn(SimpleValue) -> SimpleValue, input: SimpleValue) -> SimpleValue {
    // Apply the arrow twice: compose it with itself
    let after_first = arrow_fn(input);
    arrow_fn(after_first)
}

pub fn apply_twice_composition(
    arrow_fn: fn(SimpleValue) -> SimpleValue,
    input: SimpleValue,
) -> SimpleValue {
    // Express as composition: f >>> f
    // This is the "arrow way" to express apply_twice
    let result1 = arrow_fn(input);
    arrow_fn(result1)
}

// ============================================================================
// Experiment 2: Higher-Order Arrow - Map
// ============================================================================
// Test: Can we express list mapping via arrow composition?
// Pattern: map f [a, b, c] = [f(a), f(b), f(c)]
// Arrow version: map :: (a ~> b) -> [a] ~> [b]
//                map f arr_list = arr_list >>> (arr (λxs. map_arrow f xs))

pub fn map_arrow(arrow_fn: fn(SimpleValue) -> SimpleValue, list: SimpleValue) -> SimpleValue {
    match list {
        SimpleValue::List(items) => {
            let mapped: Vec<SimpleValue> = items.into_iter().map(|item| arrow_fn(item)).collect();
            SimpleValue::List(mapped)
        }
        _ => SimpleValue::Unit,
    }
}

// ============================================================================
// Experiment 3: Higher-Order Arrow - Filter
// ============================================================================
// Test: Can we express list filtering via arrow composition?
// Pattern: filter p [a, b, c] = [x | x in [a,b,c], p(x)]
// Arrow version: filter :: (a ~> Bool) -> [a] ~> [a]
//                filter p arr_list = arr_list >>> (arr (λxs. filter_arrow p xs))

pub fn filter_arrow(predicate: fn(SimpleValue) -> SimpleValue, list: SimpleValue) -> SimpleValue {
    match list {
        SimpleValue::List(items) => {
            let filtered: Vec<SimpleValue> = items
                .into_iter()
                .filter(|item| {
                    let result = predicate(item.clone());
                    matches!(result, SimpleValue::Bool(true))
                })
                .collect();
            SimpleValue::List(filtered)
        }
        _ => SimpleValue::Unit,
    }
}

// ============================================================================
// Experiment 4: Pipe Combinator
// ============================================================================
// Test: Can we define a combinator that chains arrows together?
// Pattern: pipe [f, g, h] x = h(g(f(x)))
// Arrow version: A way to compose a list of arrows sequentially

pub fn pipe_arrows(
    arrows: Vec<fn(SimpleValue) -> SimpleValue>,
    input: SimpleValue,
) -> SimpleValue {
    let mut result = input;
    for arrow_fn in arrows {
        result = arrow_fn(result);
    }
    result
}

// ============================================================================
// Experiment 5: Parametric Arrow - Fold
// ============================================================================
// Test: Can we express fold/reduce as a parametric arrow?
// Pattern: fold f init [a, b, c] = f(f(f(init, a), b), c)
// Arrow version: fold :: (b ~> a -> b) -> b -> [a] ~> b
//                fold f init arr_list = arr_list >>> (arr (λxs. fold_arrow f init xs))

pub fn fold_arrow(
    step_fn: fn(SimpleValue, SimpleValue) -> SimpleValue,
    init: SimpleValue,
    list: SimpleValue,
) -> SimpleValue {
    match list {
        SimpleValue::List(items) => {
            let mut accumulator = init;
            for item in items {
                accumulator = step_fn(accumulator, item);
            }
            accumulator
        }
        _ => SimpleValue::Unit,
    }
}

// ============================================================================
// Test Suite
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Test 1: ApplyTwice with increment
    #[test]
    fn test_apply_twice_increment() {
        fn increment(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n + 1),
                _ => SimpleValue::Unit,
            }
        }

        let result = apply_twice_step(increment, SimpleValue::Int(5));
        assert_eq!(result, SimpleValue::Int(7), "increment twice on 5 should give 7");
    }

    // Test 2: ApplyTwice with multiplication
    #[test]
    fn test_apply_twice_double() {
        fn double(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n * 2),
                _ => SimpleValue::Unit,
            }
        }

        let result = apply_twice_step(double, SimpleValue::Int(5));
        assert_eq!(result, SimpleValue::Int(20), "double twice on 5 should give 20");
    }

    // Test 3: ApplyTwice composition form
    #[test]
    fn test_apply_twice_composition() {
        fn square(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n * n),
                _ => SimpleValue::Unit,
            }
        }

        let result = apply_twice_composition(square, SimpleValue::Int(3));
        assert_eq!(
            result,
            SimpleValue::Int(81),
            "square twice on 3 should give 81: (3^2)^2 = 9^2 = 81"
        );
    }

    // Test 4: Map with increment
    #[test]
    fn test_map_increment() {
        fn increment(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n + 1),
                _ => SimpleValue::Unit,
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(1),
            SimpleValue::Int(2),
            SimpleValue::Int(3),
        ]);
        let result = map_arrow(increment, input);

        let expected = SimpleValue::List(vec![
            SimpleValue::Int(2),
            SimpleValue::Int(3),
            SimpleValue::Int(4),
        ]);
        assert_eq!(result, expected, "map increment over [1,2,3] should give [2,3,4]");
    }

    // Test 5: Map with double
    #[test]
    fn test_map_double() {
        fn double(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n * 2),
                _ => SimpleValue::Unit,
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(1),
            SimpleValue::Int(2),
            SimpleValue::Int(3),
        ]);
        let result = map_arrow(double, input);

        let expected = SimpleValue::List(vec![
            SimpleValue::Int(2),
            SimpleValue::Int(4),
            SimpleValue::Int(6),
        ]);
        assert_eq!(result, expected, "map double over [1,2,3] should give [2,4,6]");
    }

    // Test 6: Filter with is_even
    #[test]
    fn test_filter_even() {
        fn is_even(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Bool(n % 2 == 0),
                _ => SimpleValue::Bool(false),
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(1),
            SimpleValue::Int(2),
            SimpleValue::Int(3),
            SimpleValue::Int(4),
            SimpleValue::Int(5),
        ]);
        let result = filter_arrow(is_even, input);

        let expected = SimpleValue::List(vec![SimpleValue::Int(2), SimpleValue::Int(4)]);
        assert_eq!(result, expected, "filter even from [1,2,3,4,5] should give [2,4]");
    }

    // Test 7: Filter with greater_than_2
    #[test]
    fn test_filter_greater_than_2() {
        fn greater_than_2(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Bool(n > 2),
                _ => SimpleValue::Bool(false),
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(1),
            SimpleValue::Int(2),
            SimpleValue::Int(3),
            SimpleValue::Int(4),
        ]);
        let result = filter_arrow(greater_than_2, input);

        let expected = SimpleValue::List(vec![SimpleValue::Int(3), SimpleValue::Int(4)]);
        assert_eq!(
            result, expected,
            "filter > 2 from [1,2,3,4] should give [3,4]"
        );
    }

    // Test 8: Pipe multiple arrows
    #[test]
    fn test_pipe_arrows() {
        fn increment(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n + 1),
                _ => SimpleValue::Unit,
            }
        }

        fn double(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n * 2),
                _ => SimpleValue::Unit,
            }
        }

        fn square(x: SimpleValue) -> SimpleValue {
            match x {
                SimpleValue::Int(n) => SimpleValue::Int(n * n),
                _ => SimpleValue::Unit,
            }
        }

        let arrows: Vec<fn(SimpleValue) -> SimpleValue> = vec![increment, double, square];
        let result = pipe_arrows(arrows, SimpleValue::Int(2));

        // (2+1)*2 = 6, 6^2 = 36
        assert_eq!(result, SimpleValue::Int(36), "pipe [+1, *2, ^2] on 2 should give 36");
    }

    // Test 9: Fold with sum
    #[test]
    fn test_fold_sum() {
        fn add(acc: SimpleValue, x: SimpleValue) -> SimpleValue {
            match (acc, x) {
                (SimpleValue::Int(a), SimpleValue::Int(b)) => SimpleValue::Int(a + b),
                _ => SimpleValue::Unit,
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(1),
            SimpleValue::Int(2),
            SimpleValue::Int(3),
        ]);
        let result = fold_arrow(add, SimpleValue::Int(0), input);

        assert_eq!(result, SimpleValue::Int(6), "fold sum over [1,2,3] should give 6");
    }

    // Test 10: Fold with product
    #[test]
    fn test_fold_product() {
        fn multiply(acc: SimpleValue, x: SimpleValue) -> SimpleValue {
            match (acc, x) {
                (SimpleValue::Int(a), SimpleValue::Int(b)) => SimpleValue::Int(a * b),
                _ => SimpleValue::Unit,
            }
        }

        let input = SimpleValue::List(vec![
            SimpleValue::Int(2),
            SimpleValue::Int(3),
            SimpleValue::Int(4),
        ]);
        let result = fold_arrow(multiply, SimpleValue::Int(1), input);

        assert_eq!(result, SimpleValue::Int(24), "fold product over [2,3,4] should give 24");
    }
}

fn main() {
    println!("Arrow Calculus: Challenge #2 - Higher-Order Arrows");
    println!("==================================================\n");

    // Test 1: ApplyTwice
    println!("Test 1: ApplyTwice with Increment");
    fn increment(x: SimpleValue) -> SimpleValue {
        match x {
            SimpleValue::Int(n) => SimpleValue::Int(n + 1),
            _ => SimpleValue::Unit,
        }
    }
    let result = apply_twice_step(increment, SimpleValue::Int(5));
    println!("  apply_twice(+1)(5) = {} (expected 7)\n", result);

    // Test 2: ApplyTwice with Double
    println!("Test 2: ApplyTwice with Double");
    fn double(x: SimpleValue) -> SimpleValue {
        match x {
            SimpleValue::Int(n) => SimpleValue::Int(n * 2),
            _ => SimpleValue::Unit,
        }
    }
    let result = apply_twice_step(double, SimpleValue::Int(5));
    println!("  apply_twice(*2)(5) = {} (expected 20)\n", result);

    // Test 3: Map
    println!("Test 3: Map with Increment");
    let input = SimpleValue::List(vec![
        SimpleValue::Int(1),
        SimpleValue::Int(2),
        SimpleValue::Int(3),
    ]);
    let result = map_arrow(increment, input);
    println!("  map(+1)([1,2,3]) = {} (expected [2,3,4])\n", result);

    // Test 4: Filter
    println!("Test 4: Filter with Even Predicate");
    fn is_even(x: SimpleValue) -> SimpleValue {
        match x {
            SimpleValue::Int(n) => SimpleValue::Bool(n % 2 == 0),
            _ => SimpleValue::Bool(false),
        }
    }
    let input = SimpleValue::List(vec![
        SimpleValue::Int(1),
        SimpleValue::Int(2),
        SimpleValue::Int(3),
        SimpleValue::Int(4),
    ]);
    let result = filter_arrow(is_even, input);
    println!("  filter(even)([1,2,3,4]) = {} (expected [2, 4])\n", result);

    // Test 5: Pipe
    println!("Test 5: Pipe Multiple Arrows");
    fn square(x: SimpleValue) -> SimpleValue {
        match x {
            SimpleValue::Int(n) => SimpleValue::Int(n * n),
            _ => SimpleValue::Unit,
        }
    }
    let arrows: Vec<fn(SimpleValue) -> SimpleValue> = vec![increment, double, square];
    let result = pipe_arrows(arrows, SimpleValue::Int(2));
    println!("  pipe([+1, *2, ^2])(2) = {} (expected 36)\n", result);
    println!("  Breakdown: 2 +1-> 3 *2-> 6 ^2-> 36\n");

    // Test 6: Fold
    println!("Test 6: Fold with Sum");
    fn add(acc: SimpleValue, x: SimpleValue) -> SimpleValue {
        match (acc, x) {
            (SimpleValue::Int(a), SimpleValue::Int(b)) => SimpleValue::Int(a + b),
            _ => SimpleValue::Unit,
        }
    }
    let input = SimpleValue::List(vec![
        SimpleValue::Int(1),
        SimpleValue::Int(2),
        SimpleValue::Int(3),
    ]);
    let result = fold_arrow(add, SimpleValue::Int(0), input);
    println!("  fold(+)([1,2,3]) = {} (expected 6)\n", result);
}
