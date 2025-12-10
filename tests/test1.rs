#![cfg(test)]

//! Comprehensive test suite for the Lisp interpreter
//!
//! This test suite thoroughly validates:
//! - set! mutations and closures
//! - Environment operations
//! - Integration with the evaluator
//! - Complex nested structures
//! - Recursion and tail call optimization
//! - Higher-order functions
//! - Edge cases and error handling

use rlisp::*;

// ============================================================================
// Helper Functions
// ============================================================================

fn eval_code(code: &str) -> Result<ValRef, ValRef> {
    let env = new_env();
    eval_str(code, &env)
}

fn eval_with_env(code: &str, env: &ValRef) -> Result<ValRef, ValRef> {
    eval_str(code, env)
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

fn list_len(val: &ValRef) -> usize {
    val.as_ref().list_len()
}

fn list_nth(val: &ValRef, n: usize) -> Option<ValRef> {
    val.as_ref().list_nth(n)
}

// ============================================================================
// Set! Tests
// ============================================================================

#[test]
fn test_set_basic_mutation() {
    let env = new_env();
    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env("(set! x 20)", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 20);
}

#[test]
fn test_set_returns_new_value() {
    let env = new_env();
    eval_with_env("(define x 10)", &env).unwrap();
    let result = eval_with_env("(set! x 42)", &env).unwrap();

    assert_number(&result, 42);
}

#[test]
fn test_set_unbound_variable_fails() {
    let env = new_env();
    let result = eval_with_env("(set! nonexistent 123)", &env);
    assert!(result.is_err());
}

#[test]
fn test_set_with_expression() {
    let env = new_env();
    eval_with_env("(define x 10)", &env).unwrap();
    eval_with_env("(define y 5)", &env).unwrap();
    eval_with_env("(set! x (+ y 15))", &env).unwrap();

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 20);
}

#[test]
fn test_set_multiple_mutations() {
    let env = new_env();
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
    let env = new_env();

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
    let env = new_env();

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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
    eval_with_env("(define flag #t)", &env).unwrap();

    let result = eval_with_env("flag", &env).unwrap();
    assert_bool(&result, true);

    eval_with_env("(set! flag #f)", &env).unwrap();
    let result = eval_with_env("flag", &env).unwrap();
    assert_bool(&result, false);
}

#[test]
fn test_set_list_value() {
    let env = new_env();
    eval_with_env("(define mylist (list 1 2 3))", &env).unwrap();
    eval_with_env("(set! mylist (list 4 5 6))", &env).unwrap();

    let result = eval_with_env("(car mylist)", &env).unwrap();
    assert_number(&result, 4);
}

#[test]
fn test_set_wrong_argument_count() {
    let env = new_env();
    eval_with_env("(define x 10)", &env).unwrap();

    // Too few arguments
    assert!(eval_with_env("(set! x)", &env).is_err());

    // Too many arguments
    assert!(eval_with_env("(set! x 20 30)", &env).is_err());
}

#[test]
fn test_set_non_symbol_first_arg() {
    let env = new_env();

    assert!(eval_with_env("(set! 123 456)", &env).is_err());
    assert!(eval_with_env("(set! (+ 1 2) 10)", &env).is_err());
}

#[test]
fn test_set_preserves_other_bindings() {
    let env = new_env();
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
    let env = new_env();

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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
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
    let env = new_env();
    eval_with_env("(define func (lambda (x) x))", &env).unwrap();
    eval_with_env("(set! func (lambda (x) (* x 2)))", &env).unwrap();

    let result = eval_with_env("(func 5)", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_set_multiple_variables_in_sequence() {
    let env = new_env();
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
    let env = new_env();
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

    let result = eval_code("(* 2 3 4)").unwrap();
    assert_number(&result, 24);

    let result = eval_code("(- 10 3 2)").unwrap();
    assert_number(&result, 5);

    let result = eval_code("(/ 100 5 2)").unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_nested_arithmetic() {
    let result = eval_code("(+ (* 2 3) (- 10 5))").unwrap();
    assert_number(&result, 11);

    let result = eval_code("(+ (* 2 3) (- 10 5) (/ 20 4))").unwrap();
    assert_number(&result, 16); // 6 + 5 + 5
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

    let result = eval_code("(> 10 5)").unwrap();
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
    let env = new_env();
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
    let env = new_env();
    eval_with_env("(define x 42)", &env).unwrap();
    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 42);

    eval_with_env("(define y (* x 2))", &env).unwrap();
    let result = eval_with_env("y", &env).unwrap();
    assert_number(&result, 84);
}

#[test]
fn test_lambda_application() {
    let result = eval_code("((lambda (x) (* x 2)) 5)").unwrap();
    assert_number(&result, 10);

    let result = eval_code("((lambda (x y) (+ x y)) 3 4)").unwrap();
    assert_number(&result, 7);

    let result = eval_code("((lambda (x) (* x x)) 5)").unwrap();
    assert_number(&result, 25);
}

#[test]
fn test_lambda_closure() {
    let env = new_env();
    eval_with_env(
        "(define make-adder (lambda (n) (lambda (x) (+ x n))))",
        &env,
    )
    .unwrap();
    eval_with_env("(define add5 (make-adder 5))", &env).unwrap();

    let result = eval_with_env("(add5 10)", &env).unwrap();
    assert_number(&result, 15);

    eval_with_env("(define add10 (make-adder 10))", &env).unwrap();
    let result = eval_with_env("(add10 5)", &env).unwrap();
    assert_number(&result, 15);
}

#[test]
fn test_list_operations() {
    let env = new_env();

    eval_with_env("(define mylist (list 1 2 3 4))", &env).unwrap();

    let result = eval_with_env("(car mylist)", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(car (cdr mylist))", &env).unwrap();
    assert_number(&result, 2);

    let result = eval_with_env("(length mylist)", &env).unwrap();
    assert_number(&result, 4);

    let result = eval_with_env("(car '(1 2 3))", &env).unwrap();
    assert_number(&result, 1);

    let result = eval_with_env("(length '(1 2 3 4 5))", &env).unwrap();
    assert_number(&result, 5);

    let result = eval_with_env("(null? ())", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(null? '(1))", &env).unwrap();
    assert_bool(&result, false);
}

#[test]
fn test_cons_operations() {
    let env = new_env();

    let result = eval_with_env("(cons 1 (cons 2 (cons 3 ())))", &env).unwrap();

    let car = eval_with_env("(car (cons 1 (cons 2 (cons 3 ()))))", &env).unwrap();
    assert_number(&car, 1);

    let result = eval_with_env("(null? ())", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(null? (cons 1 ()))", &env).unwrap();
    assert_bool(&result, false);

    let result = eval_with_env("(cons? (cons 1 2))", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(cons? 42)", &env).unwrap();
    assert_bool(&result, false);
}

#[test]
fn test_recursive_factorial() {
    let env = new_env();

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
    let env = new_env();

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
    let env = new_env();

    let result = eval_with_env("(append (list 1 2) (list 3 4))", &env).unwrap();
    let car = eval_with_env("(car (append (list 1 2) (list 3 4)))", &env).unwrap();
    assert_number(&car, 1);

    let len = eval_with_env("(length (append (list 1 2) (list 3 4)))", &env).unwrap();
    assert_number(&len, 4);
}

#[test]
fn test_reverse() {
    let env = new_env();

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
// Tail Call Optimization Tests
// ============================================================================

#[test]
fn test_simple_tail_recursion() {
    let env = new_env();

    eval_with_env(
        r#"
        (define countdown
          (lambda (n acc)
            (if (= n 0)
                acc
                (countdown (- n 1) (+ acc 1)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(countdown 100 0)", &env).unwrap();
    assert_number(&result, 100);
}

#[test]
fn test_deep_tail_recursion() {
    let env = new_env();

    eval_with_env(
        r#"
        (define sum-tail
          (lambda (n acc)
            (if (= n 0)
                acc
                (sum-tail (- n 1) (+ acc n)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(sum-tail 1000 0)", &env).unwrap();
    assert_number(&result, 500500);
}

#[test]
fn test_factorial_tail_recursive() {
    let env = new_env();

    eval_with_env(
        r#"
        (define factorial
          (lambda (n acc)
            (if (= n 0)
                acc
                (factorial (- n 1) (* n acc)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(factorial 10 1)", &env).unwrap();
    assert_number(&result, 3628800);
}

#[test]
fn test_very_deep_recursion() {
    let env = new_env();

    eval_with_env(
        r#"
        (define deep-sum
          (lambda (n acc)
            (if (= n 0)
                acc
                (deep-sum (- n 1) (+ acc 1)))))
        "#,
        &env,
    )
    .unwrap();

    // Should work with proper TCO
    let result = eval_with_env("(deep-sum 10000 0)", &env).unwrap();
    assert_number(&result, 10000);
}

// ============================================================================
// Complex Integration Tests
// ============================================================================

#[test]
fn test_higher_order_functions() {
    let env = new_env();

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

    let result = eval_with_env("(map (lambda (x) (* x x)) '(1 2 3 4))", &env).unwrap();

    let first = list_nth(&result, 0).unwrap();
    assert_number(&first, 1);

    let second = list_nth(&result, 1).unwrap();
    assert_number(&second, 4);

    let third = list_nth(&result, 2).unwrap();
    assert_number(&third, 9);

    let fourth = list_nth(&result, 3).unwrap();
    assert_number(&fourth, 16);
}

#[test]
fn test_y_combinator() {
    let env = new_env();

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
    let env = new_env();

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

    let env = new_env();
    let result = eval_str_multiple(code, &env).unwrap();
    assert_number(&result, 3);
}

#[test]
fn test_fibonacci_tree_recursion() {
    let env = new_env();

    eval_with_env(
        r#"
        (define fib
          (lambda (n)
            (if (< n 2)
                n
                (+ (fib (- n 1)) (fib (- n 2))))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(fib 10)", &env).unwrap();
    assert_number(&result, 55);

    let result = eval_with_env("(fib 15)", &env).unwrap();
    assert_number(&result, 610);
}

#[test]
fn test_mutual_recursion() {
    let env = new_env();

    eval_with_env(
        r#"
        (define is-even
          (lambda (n)
            (if (= n 0)
                #t
                (is-odd (- n 1)))))
        "#,
        &env,
    )
    .unwrap();

    eval_with_env(
        r#"
        (define is-odd
          (lambda (n)
            (if (= n 0)
                #f
                (is-even (- n 1)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(is-even 100)", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(is-odd 99)", &env).unwrap();
    assert_bool(&result, true);

    let result = eval_with_env("(is-even 1000)", &env).unwrap();
    assert_bool(&result, true);
}

#[test]
fn test_ackermann_function() {
    let env = new_env();

    eval_with_env(
        r#"
        (define ackermann
          (lambda (m n)
            (if (= m 0)
                (+ n 1)
                (if (= n 0)
                    (ackermann (- m 1) 1)
                    (ackermann (- m 1) (ackermann m (- n 1)))))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(ackermann 2 2)", &env).unwrap();
    assert_number(&result, 7);

    let result = eval_with_env("(ackermann 3 2)", &env).unwrap();
    assert_number(&result, 29);
}

#[test]
fn test_filter_function() {
    let env = new_env();

    eval_with_env(
        r#"
        (define filter
          (lambda (pred lst)
            (if (null? lst)
                ()
                (if (pred (car lst))
                    (cons (car lst) (filter pred (cdr lst)))
                    (filter pred (cdr lst))))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(filter (lambda (x) (> x 0)) '(-2 -1 0 1 2 3))", &env).unwrap();

    assert_eq!(list_len(&result), 3);

    let first = list_nth(&result, 0).unwrap();
    assert_number(&first, 1);

    let second = list_nth(&result, 1).unwrap();
    assert_number(&second, 2);

    let third = list_nth(&result, 2).unwrap();
    assert_number(&third, 3);
}

#[test]
fn test_compose_function() {
    let env = new_env();

    eval_with_env(
        r#"
        (define compose
          (lambda (f g)
            (lambda (x) (f (g x)))))
        "#,
        &env,
    )
    .unwrap();

    eval_with_env("(define add1 (lambda (x) (+ x 1)))", &env).unwrap();
    eval_with_env("(define square (lambda (x) (* x x)))", &env).unwrap();
    eval_with_env("(define composed (compose add1 square))", &env).unwrap();

    let result = eval_with_env("(composed 5)", &env).unwrap();
    assert_number(&result, 26); // square(5) + 1 = 25 + 1 = 26
}

#[test]
fn test_list_building() {
    let env = new_env();

    eval_with_env(
        r#"
        (define build-list
          (lambda (n acc)
            (if (= n 0)
                acc
                (build-list (- n 1) (cons n acc)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(build-list 100 ())", &env).unwrap();
    assert_eq!(list_len(&result), 100);

    let first = list_nth(&result, 0).unwrap();
    assert_number(&first, 1);
}

#[test]
fn test_nested_lambdas() {
    let env = new_env();

    let result = eval_with_env("((lambda (x) ((lambda (y) (+ x y)) 10)) 5)", &env).unwrap();
    assert_number(&result, 15);
}

#[test]
fn test_fold_operations() {
    let env = new_env();

    eval_with_env(
        r#"
        (define fold
          (lambda (f acc lst)
            (if (null? lst)
                acc
                (fold f (f acc (car lst)) (cdr lst)))))
        "#,
        &env,
    )
    .unwrap();

    // Sum using fold
    let result = eval_with_env(
        "(fold (lambda (a b) (+ a b)) 0 '(1 2 3 4 5 6 7 8 9 10))",
        &env,
    )
    .unwrap();
    assert_number(&result, 55);

    // Product using fold
    let result = eval_with_env("(fold (lambda (a b) (* a b)) 1 '(1 2 3 4 5))", &env).unwrap();
    assert_number(&result, 120);
}

#[test]
fn test_deeply_nested_data_structures() {
    let env = new_env();

    eval_with_env(
        r#"
        (define make-nested
          (lambda (depth val)
            (if (= depth 0)
                val
                (cons (make-nested (- depth 1) val) ()))))
        "#,
        &env,
    )
    .unwrap();

    eval_with_env(
        r#"
        (define extract-nested
          (lambda (depth lst)
            (if (= depth 0)
                lst
                (extract-nested (- depth 1) (car lst)))))
        "#,
        &env,
    )
    .unwrap();

    // Create deeply nested structure (100 levels)
    eval_with_env("(define nested (make-nested 100 42))", &env).unwrap();

    // Extract the value
    let result = eval_with_env("(extract-nested 100 nested)", &env).unwrap();
    assert_number(&result, 42);
}

#[test]
fn test_alternating_recursion_patterns() {
    let env = new_env();

    eval_with_env(
        r#"
        (define bounce
          (lambda (n mode)
            (if (= n 0)
                mode
                (if (= mode 0)
                    (bounce (- n 1) 1)
                    (bounce (- n 1) 0)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(bounce 1000 0)", &env).unwrap();
    assert_number(&result, 0); // Even number of bounces

    let result = eval_with_env("(bounce 999 0)", &env).unwrap();
    assert_number(&result, 1); // Odd number of bounces
}

#[test]
fn test_complex_computation() {
    let env = new_env();

    eval_with_env(
        r#"
        (define compute-sum
          (lambda (n)
            (if (= n 0)
                0
                (+ n (compute-sum (- n 1))))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(compute-sum 100)", &env).unwrap();
    assert_number(&result, 5050);
}

#[test]
fn test_nested_closure_chains() {
    let env = new_env();

    eval_with_env(
        r#"
        (define make-chain
          (lambda (n)
            (if (= n 0)
                (lambda (x) x)
                (lambda (x) ((make-chain (- n 1)) (+ x 1))))))
        "#,
        &env,
    )
    .unwrap();

    // Create chain of 50 closures
    eval_with_env("(define chain50 (make-chain 50))", &env).unwrap();
    let result = eval_with_env("(chain50 0)", &env).unwrap();
    assert_number(&result, 50);
}

#[test]
fn test_repeated_environment_modifications() {
    let env = new_env();

    // Define many variables
    for i in 0..50 {
        let def_expr = format!("(define var{} {})", i, i * 2);
        eval_with_env(&def_expr, &env).unwrap();
    }

    // Verify a few
    let result = eval_with_env("var0", &env).unwrap();
    assert_number(&result, 0);

    let result = eval_with_env("var25", &env).unwrap();
    assert_number(&result, 50);

    let result = eval_with_env("var49", &env).unwrap();
    assert_number(&result, 98);
}

#[test]
fn test_begin_sequencing() {
    let env = new_env();

    eval_with_env("(define x 0)", &env).unwrap();

    let result = eval_with_env("(begin (define x 10) (define y 20) (+ x y))", &env).unwrap();
    assert_number(&result, 30);

    let result = eval_with_env("x", &env).unwrap();
    assert_number(&result, 10);
}

#[test]
fn test_lambda_with_begin_body() {
    let env = new_env();

    let code = r#"
        (define test
          (lambda (n)
            (define temp (* n 2))
            (define temp2 (+ temp 5))
            temp2))
    "#;

    eval_with_env(code, &env).unwrap();
    let result = eval_with_env("(test 10)", &env).unwrap();
    assert_number(&result, 25); // 10 * 2 + 5 = 25
}

#[test]
fn test_massive_list_operations() {
    let env = new_env();

    eval_with_env(
        r#"
        (define range
          (lambda (n acc)
            (if (= n 0)
                acc
                (range (- n 1) (cons n acc)))))
        "#,
        &env,
    )
    .unwrap();

    // Create a list of 500 elements
    let result = eval_with_env("(length (range 500 ()))", &env).unwrap();
    assert_number(&result, 500);
}

#[test]
fn test_count_down_loop() {
    let env = new_env();

    eval_with_env(
        r#"
        (define count-down
          (lambda (n)
            (if (= n 0)
                0
                (count-down (- n 1)))))
        "#,
        &env,
    )
    .unwrap();

    let result = eval_with_env("(count-down 1000)", &env).unwrap();
    assert_number(&result, 0);
}
