#![cfg(test)]

//! Comprehensive test suite for the Lisp interpreter
//!
//! This test suite thoroughly validates:
//! - set! mutations and closures
//! - Environment operations
//! - Integration with the evaluator
//! - Complex nested structures
//! - Edge cases and error handling

use rlisp::*;

// ============================================================================
// Helper Functions
// ============================================================================

fn eval_code(code: &str) -> Result<ValRef, ValRef> {
    let env = env_new();
    let expr = parse(code)?;
    eval(expr, &env)
}

fn eval_with_env(code: &str, env: &ValRef) -> Result<ValRef, ValRef> {
    let expr = parse(code)?;
    eval(expr, env)
}

fn assert_number(val: &ValRef, expected: i64) {
    match val.as_ref() {
        Value::Number(n) => assert_eq!(*n, expected, "Expected {}, got {}", expected, n),
        other => panic!("Expected Number({}), got {:?}", expected, other),
    }
}

fn assert_bool(val: &ValRef, expected: bool) {
    match val.as_ref() {
        Value::Bool(b) => assert_eq!(*b, expected, "Expected {}, got {}", expected, b),
        other => panic!("Expected Bool({}), got {:?}", expected, other),
    }
}

// ============================================================================
// Set! Tests
// ============================================================================

#[test]
fn test_set_basic_mutation() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env("(set! x 20)", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 20);
}

#[test]
fn test_set_returns_new_value() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();
    let result = eval_with_env("(set! x 42)", &env).unwrap();

    assert_number(&result, 42);
}

#[test]
fn test_set_unbound_variable_fails() {
    let env = env_new();
    let result = eval_with_env("(set! nonexistent 123)", &env);
    assert!(result.is_err());
}

#[test]
fn test_set_with_expression() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env("(define y 5)", &env).unwrap();
    eval_with_env("(set! x (+ y 15))", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 20);
}

#[test]
fn test_set_multiple_mutations() {
    let env = env_new();
    eval_with_env("(define counter 0)", &env).unwrap();

    eval_with_env("(set! counter (+ counter 1))", &env).unwrap();
    let result = eval_with_env("counter", &env).unwrap();
    assert_number(&result, 1);

    eval_with_env("(set! counter (+ counter 1))", &env).unwrap();
    let result = eval_with_env("counter", &env).unwrap();
    assert_number(&result, 2);

    eval_with_env("(set! counter (+ counter 1))", &env).unwrap();
    let result = eval_with_env("counter", &env).unwrap();
    assert_number(&result, 3);
}

#[test]
fn test_set_in_lambda_closure() {
    let env = env_new();

    let code = r#"
        (define make-counter
          (lambda ()
            (define count 0)
            (lambda ()
              (set! count (+ count 1))
              count)))
    "#;
    eval_with_env(code, &env).unwrap();
    eval_with_env("(define c1 (make-counter))", &env).unwrap();

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 2);

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 3);
}

#[test]
fn test_set_independent_closures() {
    let env = env_new();

    let code = r#"
        (define make-counter
          (lambda ()
            (define count 0)
            (lambda ()
              (set! count (+ count 1))
              count)))
    "#;
    eval_with_env(code, &env).unwrap();
    eval_with_env("(define c1 (make-counter))", &env).unwrap();
    eval_with_env("(define c2 (make-counter))", &env).unwrap();

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 2);

    let result = eval_with_env("(c2)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(c1)", &env).unwrap();
    assert_number(&result, 3);

    let result = eval_with_env("(c2)", &env).unwrap();
    assert_number(&result, 2);
}

#[test]
fn test_set_in_nested_scope() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();

    let code = r#"
        (define mutate-x
          (lambda (val)
            (set! x val)))
    "#;
    eval_with_env(code, &env).unwrap();
    eval_with_env("(mutate-x 42)", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 42);
}

#[test]
fn test_set_shadowed_variable() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();

    let code = r#"
        (define test
          (lambda ()
            (define x 20)
            (set! x 30)
            x))
    "#;
    eval_with_env(code, &env).unwrap();

    let result = eval_with_env("(test)", &env).unwrap();
    assert_number(&result, 30);

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_set_boolean_value() {
    let env = env_new();
    eval_with_env("(define flag #t)", &env).unwrap();

    let result = eval_with_env("flag", &env).unwrap();
    assert_bool(&result, true);

    eval_with_env("(set! flag #f)", &env).unwrap();
    let result = eval_with_env("flag", &env).unwrap();
    assert_bool(&result, false);
}

#[test]
fn test_set_list_value() {
    let env = env_new();
    eval_with_env("(define mylist (list 1 2 3))", &env).unwrap();
    eval_with_env("(set! mylist (list 4 5 6))", &env).unwrap();

    let result = eval_with_env("(car mylist)", &env).unwrap();
    assert_number(&result, 4);
}

#[test]
fn test_set_wrong_argument_count() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();

    // Too few arguments
    assert!(eval_with_env("(set! x)", &env).is_err());

    // Too many arguments
    assert!(eval_with_env("(set! x 20 30)", &env).is_err());
}

#[test]
fn test_set_non_symbol_first_arg() {
    let env = env_new();

    assert!(eval_with_env("(set! 123 456)", &env).is_err());
    assert!(eval_with_env("(set! (+ 1 2) 10)", &env).is_err());
}

#[test]
fn test_set_preserves_other_bindings() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env("(define y 20)", &env).unwrap();
    eval_with_env("(define z 30)", &env).unwrap();
    eval_with_env("(set! y 99)", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 10);

    let result = eval_with_env("y", &env).unwrap();
    assert_number(&result, 99);

    let result = eval_with_env("z", &env).unwrap();
    assert_number(&result, 30);
}

#[test]
fn test_set_bank_account_example() {
    let env = env_new();

    let code = r#"
        (define make-account
          (lambda (balance)
            (lambda (amount)
              (set! balance (+ balance amount))
              balance)))
    "#;
    eval_with_env(code, &env).unwrap();
    eval_with_env("(define acc (make-account 100))", &env).unwrap();

    let result = eval_with_env("(acc 50)", &env).unwrap();
    assert_number(&result, 150);

    let result = eval_with_env("(acc -25)", &env).unwrap();
    assert_number(&result, 125);

    let result = eval_with_env("(acc 10)", &env).unwrap();
    assert_number(&result, 135);
}

#[test]
fn test_set_parent_scope() {
    let env = env_new();
    eval_with_env("(define x 100)", &env).unwrap();
    eval_with_env(
        "(define mutate-x (lambda (new-val) (set! x new-val)))",
        &env,
    )
    .unwrap();
    eval_with_env("(mutate-x 200)", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 200);
}

#[test]
fn test_set_vs_define_shadowing() {
    let env = env_new();
    eval_with_env("(define x 10)", &env).unwrap();

    let code = r#"
        (define test
          (lambda ()
            (define x 20)
            (set! x 30)
            x))
    "#;
    eval_with_env(code, &env).unwrap();

    let result = eval_with_env("(test)", &env).unwrap();
    assert_number(&result, 30);

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_set_finds_first_binding_in_chain() {
    let env = env_new();
    eval_with_env("(define x 1)", &env).unwrap();
    eval_with_env(
        "(define outer (lambda () (define x 2) (define inner (lambda () (set! x 99))) (inner) x))",
        &env,
    )
    .unwrap();

    let result = eval_with_env("(outer)", &env).unwrap();
    assert_number(&result, 99);

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 1);
}

#[test]
fn test_set_accumulator_pattern() {
    let env = env_new();
    eval_with_env("(define sum 0)", &env).unwrap();
    eval_with_env(
        "(define add-to-sum (lambda (n) (set! sum (+ sum n)) sum))",
        &env,
    )
    .unwrap();

    let result = eval_with_env("(add-to-sum 5)", &env).unwrap();
    assert_number(&result, 5);

    let result = eval_with_env("(add-to-sum 10)", &env).unwrap();
    assert_number(&result, 15);

    let result = eval_with_env("(add-to-sum 7)", &env).unwrap();
    assert_number(&result, 22);
}

#[test]
fn test_set_swap_pattern() {
    let env = env_new();
    eval_with_env("(define a 10)", &env).unwrap();
    eval_with_env("(define b 20)", &env).unwrap();
    eval_with_env("(define temp a)", &env).unwrap();
    eval_with_env("(set! a b)", &env).unwrap();
    eval_with_env("(set! b temp)", &env).unwrap();

    let result = eval_with_env("a", &env).unwrap();
    assert_number(&result, 20);

    let result = eval_with_env("b", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_set_in_recursive_function() {
    let env = env_new();
    eval_with_env("(define call-count 0)", &env).unwrap();
    eval_with_env(
        "(define counting-factorial (lambda (n) (set! call-count (+ call-count 1)) (if (= n 0) 1 (* n (counting-factorial (- n 1))))))",
        &env,
    ).unwrap();

    eval_with_env("(counting-factorial 5)", &env).unwrap();

    let result = eval_with_env("call-count", &env).unwrap();
    assert_number(&result, 6);
}

#[test]
fn test_set_with_lambda_value() {
    let env = env_new();
    eval_with_env("(define func (lambda (x) x))", &env).unwrap();
    eval_with_env("(set! func (lambda (x) (* x 2)))", &env).unwrap();

    let result = eval_with_env("(func 5)", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_set_multiple_variables_in_sequence() {
    let env = env_new();
    eval_with_env("(define a 1)", &env).unwrap();
    eval_with_env("(define b 2)", &env).unwrap();
    eval_with_env("(define c 3)", &env).unwrap();

    eval_with_env("(set! a 10)", &env).unwrap();
    eval_with_env("(set! b 20)", &env).unwrap();
    eval_with_env("(set! c 30)", &env).unwrap();

    let result = eval_with_env("(+ a b c)", &env).unwrap();
    assert_number(&result, 60);
}

#[test]
fn test_set_state_machine() {
    let env = env_new();
    eval_with_env("(define state 0)", &env).unwrap();
    eval_with_env(
        "(define toggle (lambda () (if (= state 0) (set! state 1) (set! state 0)) state))",
        &env,
    )
    .unwrap();

    let result = eval_with_env("(toggle)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(toggle)", &env).unwrap();
    assert_number(&result, 0);

    let result = eval_with_env("(toggle)", &env).unwrap();
    assert_number(&result, 1);
}

// ============================================================================
// Basic Evaluation Tests
// ============================================================================

#[test]
fn test_basic_arithmetic() {
    let result = eval_code("(+ 1 2 3)").unwrap();
    assert_number(&result, 6);

    let result = eval_code("(- 10 3)").unwrap();
    assert_number(&result, 7);

    let result = eval_code("(* 4 5)").unwrap();
    assert_number(&result, 20);

    let result = eval_code("(/ 20 4)").unwrap();
    assert_number(&result, 5);
}

#[test]
fn test_nested_arithmetic() {
    let result = eval_code("(+ (* 2 3) (- 10 5))").unwrap();
    assert_number(&result, 11);
}

#[test]
fn test_comparison_operators() {
    let result = eval_code("(= 5 5)").unwrap();
    assert_bool(&result, true);

    let result = eval_code("(= 5 6)").unwrap();
    assert_bool(&result, false);

    let result = eval_code("(< 3 5)").unwrap();
    assert_bool(&result, true);

    let result = eval_code("(> 5 3)").unwrap();
    assert_bool(&result, true);
}

#[test]
fn test_if_expression() {
    let result = eval_code("(if #t 1 2)").unwrap();
    assert_number(&result, 1);

    let result = eval_code("(if #f 1 2)").unwrap();
    assert_number(&result, 2);

    let result = eval_code("(if (< 3 5) 10 20)").unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_quote() {
    let env = env_new();
    let result = eval_with_env("'(1 2 3)", &env).unwrap();

    // Verify it's a list
    match result.as_ref() {
        Value::Cons(_) => {
            let car = eval_with_env("(car '(1 2 3))", &env).unwrap();
            assert_number(&car, 1);
        }
        other => panic!("Expected Cons, got {:?}", other),
    }
}

#[test]
fn test_define_and_lookup() {
    let env = env_new();
    eval_with_env("(define x 42)", &env).unwrap();
    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 42);
}

#[test]
fn test_lambda_application() {
    let result = eval_code("((lambda (x) (* x 2)) 5)").unwrap();
    assert_number(&result, 10);

    let result = eval_code("((lambda (x y) (+ x y)) 3 4)").unwrap();
    assert_number(&result, 7);
}

#[test]
fn test_lambda_closure() {
    let env = env_new();
    eval_with_env(
        "(define make-adder (lambda (n) (lambda (x) (+ x n))))",
        &env,
    )
    .unwrap();
    eval_with_env("(define add5 (make-adder 5))", &env).unwrap();

    let result = eval_with_env("(add5 10)", &env).unwrap();
    assert_number(&result, 15);
}

#[test]
fn test_list_operations() {
    let env = env_new();

    eval_with_env("(define mylist (list 1 2 3 4))", &env).unwrap();

    let result = eval_with_env("(car mylist)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(car (cdr mylist))", &env).unwrap();
    assert_number(&result, 2);

    let result = eval_with_env("(length mylist)", &env).unwrap();
    assert_number(&result, 4);
}

#[test]
fn test_cons_operations() {
    let env = env_new();

    let result = eval_with_env("(cons 1 (cons 2 (cons 3 ())))", &env).unwrap();

    let car = eval_with_env("(car (cons 1 (cons 2 (cons 3 ()))))", &env).unwrap();
    assert_number(&car, 1);

    let result = eval_with_env("(null? ())", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(null? (cons 1 ()))", &env).unwrap();
    assert_bool(&result, false);
}

#[test]
fn test_recursive_factorial() {
    let env = env_new();

    let factorial_def = r#"
        (define factorial
          (lambda (n)
            (if (= n 0)
                1
                (* n (factorial (- n 1))))))
    "#;

    eval_with_env(factorial_def, &env).unwrap();

    let result = eval_with_env("(factorial 5)", &env).unwrap();
    assert_number(&result, 120);

    let result = eval_with_env("(factorial 10)", &env).unwrap();
    assert_number(&result, 3628800);
}

#[test]
fn test_tail_recursive_sum() {
    let env = env_new();

    let sum_def = r#"
        (define sum
          (lambda (n acc)
            (if (= n 0)
                acc
                (sum (- n 1) (+ acc n)))))
    "#;

    eval_with_env(sum_def, &env).unwrap();

    let result = eval_with_env("(sum 100 0)", &env).unwrap();
    assert_number(&result, 5050);

    // This should work without stack overflow due to TCO
    let result = eval_with_env("(sum 1000 0)", &env).unwrap();
    assert_number(&result, 500500);
}

#[test]
fn test_append() {
    let env = env_new();

    let result = eval_with_env("(append (list 1 2) (list 3 4))", &env).unwrap();
    let car = eval_with_env("(car (append (list 1 2) (list 3 4)))", &env).unwrap();
    assert_number(&car, 1);

    let len = eval_with_env("(length (append (list 1 2) (list 3 4)))", &env).unwrap();
    assert_number(&len, 4);
}

#[test]
fn test_reverse() {
    let env = env_new();

    let result = eval_with_env("(reverse (list 1 2 3))", &env).unwrap();
    let car = eval_with_env("(car (reverse (list 1 2 3)))", &env).unwrap();
    assert_number(&car, 3);
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_unbound_variable() {
    let result = eval_code("undefined-var");
    assert!(result.is_err());
}

#[test]
fn test_division_by_zero() {
    let result = eval_code("(/ 10 0)");
    assert!(result.is_err());
}

#[test]
fn test_invalid_function_call() {
    let result = eval_code("(42 1 2 3)");
    assert!(result.is_err());
}

#[test]
fn test_lambda_arity_mismatch() {
    let result = eval_code("((lambda (x y) (+ x y)) 1)");
    assert!(result.is_err());

    let result = eval_code("((lambda (x) (* x 2)) 1 2)");
    assert!(result.is_err());
}

#[test]
fn test_car_on_non_cons() {
    let result = eval_code("(car 42)");
    assert!(result.is_err());
}

#[test]
fn test_type_error_in_arithmetic() {
    let result = eval_code("(+ 1 #t)");
    assert!(result.is_err());
}

// ============================================================================
// Complex Integration Tests
// ============================================================================

#[test]
fn test_higher_order_functions() {
    let env = env_new();

    let code = r#"
        (define map
          (lambda (f lst)
            (if (null? lst)
                ()
                (cons (f (car lst)) (map f (cdr lst))))))
    "#;

    eval_with_env(code, &env).unwrap();
    eval_with_env("(define double (lambda (x) (* x 2)))", &env).unwrap();

    let result = eval_with_env("(car (map double (list 1 2 3)))", &env).unwrap();
    assert_number(&result, 2);
}

#[test]
fn test_y_combinator() {
    let env = env_new();

    let y_comb = r#"
        (define Y
          (lambda (f)
            ((lambda (x) (f (lambda (y) ((x x) y))))
             (lambda (x) (f (lambda (y) ((x x) y)))))))
    "#;

    eval_with_env(y_comb, &env).unwrap();

    let fact = r#"
        (define fact
          (Y (lambda (f)
               (lambda (n)
                 (if (= n 0)
                     1
                     (* n (f (- n 1))))))))
    "#;

    eval_with_env(fact, &env).unwrap();

    let result = eval_with_env("(fact 5)", &env).unwrap();
    assert_number(&result, 120);
}

#[test]
fn test_lexical_scoping() {
    let env = env_new();

    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env(
        "(define make-closure (lambda () (define x 20) (lambda () x)))",
        &env,
    )
    .unwrap();
    eval_with_env("(define get-x (make-closure))", &env).unwrap();

    let result = eval_with_env("(get-x)", &env).unwrap();
    assert_number(&result, 20);

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_parse_multiple_expressions() {
    let code = r#"
        (define x 1)
        (define y 2)
        (+ x y)
    "#;

    let env = env_new();
    let exprs = parse_multiple(code).unwrap();

    let mut result = ValRef::nil();
    let mut current = exprs;

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (expr, rest) = cell.borrow().clone();
                result = eval(expr, &env).unwrap();
                current = rest;
            }
            Value::Nil => break,
            _ => panic!("Invalid expression list"),
        }
    }

    assert_number(&result, 3);
}
