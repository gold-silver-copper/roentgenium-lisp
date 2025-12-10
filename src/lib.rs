#![no_std]

extern crate alloc;
use alloc::format;
use alloc::rc::Rc;
use alloc::string::{String, ToString};
use core::cell::RefCell;
use core::ops::Deref;

// ============================================================================
// Optimized Value Type - Symbols use String
// ============================================================================

pub type BuiltinFn = fn(&ValRef) -> Result<ValRef, ValRef>;

#[derive(Clone)]
pub enum Value {
    Number(i64),
    Symbol(String),
    Bool(bool),
    Char(char),
    Cons(Rc<RefCell<(ValRef, ValRef)>>),
    Builtin(BuiltinFn),
    Lambda {
        params: ValRef,
        body: ValRef,
        env: ValRef,
    },
    Nil,
}

// Manual Debug implementation
impl core::fmt::Debug for Value {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Value::Number(n) => write!(f, "Number({})", n),
            Value::Symbol(s) => write!(f, "Symbol({})", s),
            Value::Bool(b) => write!(f, "Bool({:?})", b),
            Value::Char(c) => write!(f, "Char({:?})", c),
            Value::Cons(_) => write!(f, "Cons(...)"),
            Value::Builtin(_) => write!(f, "Builtin(<fn>)"),
            Value::Lambda { .. } => write!(f, "Lambda(<fn>)"),
            Value::Nil => write!(f, "()"),
        }
    }
}

// ============================================================================
// Trampoline System for Proper TCO
// ============================================================================

pub enum EvalResult {
    Done(ValRef),
    TailCall(ValRef, ValRef),
}

// ============================================================================
// ValRef - Newtype wrapper around Rc<Value>
// ============================================================================

#[derive(Clone, Debug)]
pub struct ValRef(pub Rc<Value>);

impl ValRef {
    pub fn new(value: Value) -> Self {
        ValRef(Rc::new(value))
    }

    pub fn to_display_str(&self) -> Result<String, ()> {
        self.as_ref().to_display_str()
    }

    pub fn number(n: i64) -> Self {
        Self::new(Value::Number(n))
    }

    pub fn symbol(s: String) -> Self {
        Self::new(Value::Symbol(s))
    }

    pub fn bool_val(b: bool) -> Self {
        Self::new(Value::Bool(b))
    }

    pub fn char_val(c: char) -> Self {
        Self::new(Value::Char(c))
    }

    pub fn cons(car: ValRef, cdr: ValRef) -> Self {
        Self::new(Value::Cons(Rc::new(RefCell::new((car, cdr)))))
    }

    pub fn builtin(f: BuiltinFn) -> Self {
        Self::new(Value::Builtin(f))
    }

    pub fn lambda(params: ValRef, body: ValRef, env: ValRef) -> Self {
        Self::new(Value::Lambda { params, body, env })
    }

    pub fn nil() -> Self {
        Self::new(Value::Nil)
    }
}

impl Deref for ValRef {
    type Target = Value;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<Value> for ValRef {
    fn as_ref(&self) -> &Value {
        &self.0
    }
}

impl From<Value> for ValRef {
    fn from(value: Value) -> Self {
        ValRef::new(value)
    }
}

impl From<Rc<Value>> for ValRef {
    fn from(rc: Rc<Value>) -> Self {
        ValRef(rc)
    }
}

impl Value {
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Number(_) => "number",
            Value::Symbol(_) => "symbol",
            Value::Bool(_) => "bool",
            Value::Char(_) => "char",
            Value::Cons(_) => "cons",
            Value::Builtin(_) => "builtin",
            Value::Lambda { .. } => "lambda",
            Value::Nil => "empty-list",
        }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub fn as_number(&self) -> Option<i64> {
        match self {
            Value::Number(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_char(&self) -> Option<char> {
        match self {
            Value::Char(c) => Some(*c),
            _ => None,
        }
    }

    pub fn as_symbol(&self) -> Option<&String> {
        match self {
            Value::Symbol(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_cons(&self) -> Option<&Rc<RefCell<(ValRef, ValRef)>>> {
        match self {
            Value::Cons(cell) => Some(cell),
            _ => None,
        }
    }

    pub fn as_builtin(&self) -> Option<BuiltinFn> {
        match self {
            Value::Builtin(f) => Some(*f),
            _ => None,
        }
    }

    pub fn as_lambda(&self) -> Option<(&ValRef, &ValRef, &ValRef)> {
        match self {
            Value::Lambda { params, body, env } => Some((params, body, env)),
            _ => None,
        }
    }

    pub fn is_callable(&self) -> bool {
        matches!(self, Value::Builtin(_) | Value::Lambda { .. })
    }

    pub fn is_nil(&self) -> bool {
        matches!(self, Value::Nil)
    }

    pub fn to_display_str(&self) -> Result<String, ()> {
        match self {
            Value::Number(n) => Ok(format!("{}", n)),
            Value::Symbol(s) => Ok(s.clone()),
            Value::Bool(b) => Ok(if *b {
                String::from("#t")
            } else {
                String::from("#f")
            }),
            Value::Char(c) => Ok(c.to_string()),
            Value::Cons(_) => self.list_to_display_str(),
            Value::Builtin(_) => Ok(String::from("<builtin>")),
            Value::Lambda { .. } => Ok(String::from("<lambda>")),
            Value::Nil => Ok(String::from("()")),
        }
    }

    fn list_to_display_str(&self) -> Result<String, ()> {
        let mut result = String::from("(");
        let mut current = ValRef::new(self.clone());
        let mut first = true;

        loop {
            match current.as_ref() {
                Value::Cons(cell) => {
                    let (car, cdr) = cell.borrow().clone();
                    if !first {
                        result.push(' ');
                    }
                    first = false;

                    result.push_str(&car.as_ref().to_display_str()?);
                    current = cdr;
                }
                Value::Nil => break,
                _ => {
                    if !first {
                        result.push_str(" . ");
                    }
                    result.push_str(&current.as_ref().to_display_str()?);
                    break;
                }
            }
        }

        result.push(')');
        Ok(result)
    }

    fn list_len(&self) -> usize {
        let mut count = 0;
        let mut current = ValRef::new(self.clone());

        loop {
            match current.as_ref() {
                Value::Cons(cell) => {
                    count += 1;
                    let (_, cdr) = cell.borrow().clone();
                    current = cdr;
                }
                Value::Nil => break,
                _ => break,
            }
        }

        count
    }

    fn list_nth(&self, n: usize) -> Option<ValRef> {
        let mut current = ValRef::new(self.clone());
        let mut idx = 0;

        loop {
            match current.as_ref() {
                Value::Cons(cell) => {
                    let (car, cdr) = cell.borrow().clone();
                    if idx == n {
                        return Some(car);
                    }
                    idx += 1;
                    current = cdr;
                }
                _ => return None,
            }
        }
    }
}

// ============================================================================
// Environment Operations
// ============================================================================

pub fn env_new() -> ValRef {
    let env = ValRef::cons(ValRef::nil(), ValRef::nil());
    register_builtins(&env);
    env
}

fn env_with_parent(parent: ValRef) -> ValRef {
    ValRef::cons(ValRef::nil(), parent)
}

fn env_set(env: &ValRef, name: String, value: ValRef) {
    if let Some(cell) = env.as_cons() {
        let (bindings, parent) = cell.borrow().clone();
        let new_binding = ValRef::cons(ValRef::symbol(name), value);
        let new_bindings = ValRef::cons(new_binding, bindings);
        *cell.borrow_mut() = (new_bindings, parent);
    }
}

fn env_get(env: &ValRef, name: &str) -> Option<ValRef> {
    match env.as_ref() {
        Value::Cons(cell) => {
            let (bindings, parent) = cell.borrow().clone();

            let mut current = bindings;
            loop {
                match current.as_ref() {
                    Value::Cons(binding_cell) => {
                        let (binding, rest) = binding_cell.borrow().clone();
                        if let Value::Cons(key_value_cell) = binding.as_ref() {
                            let (key, value) = key_value_cell.borrow().clone();
                            if let Value::Symbol(s) = key.as_ref() {
                                if s.as_str() == name {
                                    return Some(value);
                                }
                            }
                        }
                        current = rest;
                    }
                    Value::Nil => break,
                    _ => break,
                }
            }

            if !parent.is_nil() {
                env_get(&parent, name)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn env_set_existing(env: &ValRef, name: &str, value: ValRef) -> Result<(), ()> {
    match env.as_ref() {
        Value::Cons(cell) => {
            let (bindings, parent) = cell.borrow().clone();

            let mut current = bindings;
            loop {
                match current.as_ref() {
                    Value::Cons(binding_cell) => {
                        let (binding, rest) = binding_cell.borrow().clone();
                        if let Value::Cons(key_value_cell) = binding.as_ref() {
                            let (key, _) = key_value_cell.borrow().clone();
                            if let Value::Symbol(s) = key.as_ref() {
                                if s.as_str() == name {
                                    *key_value_cell.borrow_mut() = (key, value);
                                    return Ok(());
                                }
                            }
                        }
                        current = rest;
                    }
                    Value::Nil => break,
                    _ => break,
                }
            }

            if !parent.is_nil() {
                env_set_existing(&parent, name, value)
            } else {
                Err(())
            }
        }
        _ => Err(()),
    }
}

fn register_builtins(env: &ValRef) {
    env_set(env, String::from("+"), ValRef::builtin(builtin_add));
    env_set(env, String::from("-"), ValRef::builtin(builtin_sub));
    env_set(env, String::from("*"), ValRef::builtin(builtin_mul));
    env_set(env, String::from("/"), ValRef::builtin(builtin_div));
    env_set(env, String::from("="), ValRef::builtin(builtin_eq));
    env_set(env, String::from("<"), ValRef::builtin(builtin_lt));
    env_set(env, String::from(">"), ValRef::builtin(builtin_gt));
    env_set(env, String::from("list"), ValRef::builtin(builtin_list));
    env_set(env, String::from("car"), ValRef::builtin(builtin_car));
    env_set(env, String::from("cdr"), ValRef::builtin(builtin_cdr));
    env_set(env, String::from("cons"), ValRef::builtin(builtin_cons_fn));
    env_set(env, String::from("null?"), ValRef::builtin(builtin_null));
    env_set(env, String::from("cons?"), ValRef::builtin(builtin_cons_p));
    env_set(env, String::from("length"), ValRef::builtin(builtin_length));
    env_set(env, String::from("append"), ValRef::builtin(builtin_append));
    env_set(
        env,
        String::from("reverse"),
        ValRef::builtin(builtin_reverse),
    );
}

// ============================================================================
// Tokenizer
// ============================================================================

fn parse_i64(s: &str) -> Result<i64, ()> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return Err(());
    }

    let (negative, start) = if bytes[0] == b'-' {
        if bytes.len() == 1 {
            return Err(());
        }
        (true, 1)
    } else if bytes[0] == b'+' {
        if bytes.len() == 1 {
            return Err(());
        }
        (false, 1)
    } else {
        (false, 0)
    };

    if bytes[start..].is_empty() {
        return Err(());
    }

    let mut result: i64 = 0;
    for &b in &bytes[start..] {
        if !(b'0'..=b'9').contains(&b) {
            return Err(());
        }
        let digit = (b - b'0') as i64;
        result = result
            .checked_mul(10)
            .and_then(|r| r.checked_add(digit))
            .ok_or(())?;
    }

    if negative {
        result.checked_neg().ok_or(())
    } else {
        Ok(result)
    }
}

fn tokenize(input: &str) -> Result<ValRef, ValRef> {
    let mut result = ValRef::nil();
    let mut chars = input.chars().peekable();

    while let Some(&ch) = chars.peek() {
        match ch {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            '(' => {
                result = ValRef::cons(ValRef::symbol(String::from("(")), result);
                chars.next();
            }
            ')' => {
                result = ValRef::cons(ValRef::symbol(String::from(")")), result);
                chars.next();
            }
            '\'' => {
                result = ValRef::cons(ValRef::symbol(String::from("'")), result);
                chars.next();
            }
            ';' => {
                while let Some(&c) = chars.peek() {
                    chars.next();
                    if c == '\n' {
                        break;
                    }
                }
            }
            '#' => {
                chars.next();
                match chars.peek() {
                    Some(&'t') => {
                        result = ValRef::cons(ValRef::bool_val(true), result);
                        chars.next();
                    }
                    Some(&'f') => {
                        result = ValRef::cons(ValRef::bool_val(false), result);
                        chars.next();
                    }
                    _ => return Err(ValRef::symbol(String::from("Invalid boolean literal"))),
                }
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == '\'' {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }

                if atom.is_empty() {
                    continue;
                }

                if let Ok(num) = parse_i64(&atom) {
                    result = ValRef::cons(ValRef::number(num), result);
                } else {
                    result = ValRef::cons(ValRef::symbol(atom), result);
                }
            }
        }
    }

    Ok(reverse_list(result))
}

fn reverse_list(list: ValRef) -> ValRef {
    let mut result = ValRef::nil();
    let mut current = list;

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (car, cdr) = cell.borrow().clone();
                result = ValRef::cons(car, result);
                current = cdr;
            }
            Value::Nil => break,
            _ => break,
        }
    }

    result
}

// ============================================================================
// Parser
// ============================================================================

fn parse_tokens(tokens: ValRef) -> Result<(ValRef, ValRef), ValRef> {
    match tokens.as_ref() {
        Value::Nil => Err(ValRef::symbol(String::from("Unexpected end of input"))),
        Value::Cons(cell) => {
            let (first, rest) = cell.borrow().clone();
            match first.as_ref() {
                Value::Number(_) | Value::Bool(_) => Ok((first, rest)),
                Value::Symbol(s) => {
                    if s == "'" {
                        if let Value::Cons(next_cell) = rest.as_ref() {
                            let (next_expr, remaining) = next_cell.borrow().clone();
                            let (val, consumed) = parse_tokens(ValRef::cons(next_expr, remaining))?;
                            let quoted = ValRef::cons(
                                ValRef::symbol(String::from("quote")),
                                ValRef::cons(val, ValRef::nil()),
                            );
                            Ok((quoted, consumed))
                        } else {
                            Err(ValRef::symbol(String::from("Quote requires an expression")))
                        }
                    } else if s == "(" {
                        let mut items = ValRef::nil();
                        let mut pos = rest;

                        loop {
                            match pos.as_ref() {
                                Value::Nil => {
                                    return Err(ValRef::symbol(String::from("Unmatched '('")));
                                }
                                Value::Cons(token_cell) => {
                                    let (token, rest_tokens) = token_cell.borrow().clone();
                                    if let Value::Symbol(tok_s) = token.as_ref() {
                                        if tok_s == ")" {
                                            return Ok((reverse_list(items), rest_tokens));
                                        }
                                    }
                                    let (val, consumed) = parse_tokens(pos)?;
                                    items = ValRef::cons(val, items);
                                    pos = consumed;
                                }
                                _ => {
                                    return Err(ValRef::symbol(String::from(
                                        "Invalid token stream",
                                    )));
                                }
                            }
                        }
                    } else if s == ")" {
                        Err(ValRef::symbol(String::from("Unexpected ')'")))
                    } else {
                        Ok((first, rest))
                    }
                }
                _ => Err(ValRef::symbol(String::from("Unexpected token type"))),
            }
        }
        _ => Err(ValRef::symbol(String::from("Invalid token stream"))),
    }
}

pub fn parse(input: &str) -> Result<ValRef, ValRef> {
    let tokens = tokenize(input)?;
    if tokens.is_nil() {
        return Err(ValRef::symbol(String::from("Empty input")));
    }
    let (val, remaining) = parse_tokens(tokens)?;
    if !remaining.is_nil() {
        return Err(ValRef::symbol(String::from(
            "Unexpected tokens after expression",
        )));
    }
    Ok(val)
}

pub fn parse_multiple(input: &str) -> Result<ValRef, ValRef> {
    let tokens = tokenize(input)?;
    if tokens.is_nil() {
        return Err(ValRef::symbol(String::from("Empty input")));
    }

    let mut expressions = ValRef::nil();
    let mut pos = tokens;

    loop {
        if pos.is_nil() {
            break;
        }
        let (val, consumed) = parse_tokens(pos)?;
        expressions = ValRef::cons(val, expressions);
        pos = consumed;
    }

    Ok(reverse_list(expressions))
}

// ============================================================================
// Evaluator
// ============================================================================

fn eval_step(expr: ValRef, env: &ValRef) -> Result<EvalResult, ValRef> {
    match expr.as_ref() {
        Value::Number(_)
        | Value::Bool(_)
        | Value::Char(_)
        | Value::Builtin(_)
        | Value::Lambda { .. } => Ok(EvalResult::Done(expr.clone())),
        Value::Symbol(s) => env_get(env, s)
            .map(EvalResult::Done)
            .ok_or_else(|| ValRef::symbol(String::from("Unbound symbol"))),
        Value::Cons(cell) => {
            let (car, cdr) = cell.borrow().clone();
            if let Value::Symbol(sym) = car.as_ref() {
                match sym.as_str() {
                    "define" => {
                        let len = expr.as_ref().list_len();
                        if len != 3 {
                            return Err(ValRef::symbol(String::from(
                                "define requires 2 arguments",
                            )));
                        }
                        let name_val = expr
                            .as_ref()
                            .list_nth(1)
                            .ok_or(ValRef::symbol(String::from("define missing name")))?;
                        let name = name_val
                            .as_symbol()
                            .ok_or(ValRef::symbol(String::from(
                                "define requires symbol as first arg",
                            )))?
                            .clone();
                        let body_val = expr
                            .as_ref()
                            .list_nth(2)
                            .ok_or(ValRef::symbol(String::from("define missing body")))?;
                        let val = eval(body_val, env)?;
                        env_set(env, name, val.clone());
                        return Ok(EvalResult::Done(val));
                    }
                    "set!" => {
                        let len = expr.as_ref().list_len();
                        if len != 3 {
                            return Err(ValRef::symbol(String::from("set! requires 2 arguments")));
                        }
                        let name_val = expr
                            .as_ref()
                            .list_nth(1)
                            .ok_or(ValRef::symbol(String::from("set! missing name")))?;
                        let name = name_val.as_symbol().ok_or(ValRef::symbol(String::from(
                            "set! requires symbol as first arg",
                        )))?;
                        let body_val = expr
                            .as_ref()
                            .list_nth(2)
                            .ok_or(ValRef::symbol(String::from("set! missing value")))?;
                        let val = eval(body_val, env)?;
                        env_set_existing(env, name, val.clone())
                            .map_err(|_| ValRef::symbol(String::from("set! unbound variable")))?;
                        return Ok(EvalResult::Done(val));
                    }

                    "lambda" => {
                        let len = expr.as_ref().list_len();
                        if len < 3 {
                            return Err(ValRef::symbol(String::from(
                                "lambda requires at least 2 arguments (params body)",
                            )));
                        }

                        let params_list = expr
                            .as_ref()
                            .list_nth(1)
                            .ok_or(ValRef::symbol(String::from("lambda missing params")))?;

                        let mut current = params_list.clone();
                        loop {
                            match current.as_ref() {
                                Value::Cons(param_cell) => {
                                    let (param, rest) = param_cell.borrow().clone();
                                    if param.as_symbol().is_none() {
                                        return Err(ValRef::symbol(String::from(
                                            "lambda params must be symbols",
                                        )));
                                    }
                                    current = rest;
                                }
                                Value::Nil => break,
                                _ => {
                                    return Err(ValRef::symbol(String::from(
                                        "lambda params must be a list",
                                    )));
                                }
                            }
                        }

                        // Collect all body expressions
                        let mut body_exprs = ValRef::nil();
                        for i in (2..len).rev() {
                            let expr_i = expr
                                .as_ref()
                                .list_nth(i)
                                .ok_or(ValRef::symbol(String::from("lambda missing body expr")))?;
                            body_exprs = ValRef::cons(expr_i, body_exprs);
                        }

                        // If multiple body expressions, wrap in begin
                        let body = if len == 3 {
                            expr.as_ref()
                                .list_nth(2)
                                .ok_or(ValRef::symbol(String::from("lambda missing body")))?
                        } else {
                            // Create (begin expr1 expr2 ...)
                            ValRef::cons(ValRef::symbol(String::from("begin")), body_exprs)
                        };

                        return Ok(EvalResult::Done(ValRef::lambda(
                            params_list,
                            body,
                            env.clone(),
                        )));
                    }
                    "begin" => {
                        let len = expr.as_ref().list_len();
                        if len < 2 {
                            return Err(ValRef::symbol(String::from(
                                "begin requires at least 1 argument",
                            )));
                        }

                        // Evaluate all expressions in sequence, return last
                        let mut result = ValRef::nil();
                        for i in 1..len {
                            let expr_i = expr
                                .as_ref()
                                .list_nth(i)
                                .ok_or(ValRef::symbol(String::from("begin missing expr")))?;

                            // For the last expression, use tail call
                            if i == len - 1 {
                                return Ok(EvalResult::TailCall(expr_i, env.clone()));
                            } else {
                                result = eval(expr_i, env)?;
                            }
                        }

                        return Ok(EvalResult::Done(result));
                    }

                    "if" => {
                        let len = expr.as_ref().list_len();
                        if len != 4 {
                            return Err(ValRef::symbol(String::from("if requires 3 arguments")));
                        }
                        let cond_expr = expr
                            .as_ref()
                            .list_nth(1)
                            .ok_or(ValRef::symbol(String::from("if missing condition")))?;
                        let cond = eval(cond_expr, env)?;
                        let is_true = match cond.as_ref() {
                            Value::Bool(b) => *b,
                            Value::Nil => false,
                            _ => true,
                        };
                        let branch_idx = if is_true { 2 } else { 3 };
                        let branch = expr
                            .as_ref()
                            .list_nth(branch_idx)
                            .ok_or(ValRef::symbol(String::from("if missing branch")))?;
                        return Ok(EvalResult::TailCall(branch, env.clone()));
                    }
                    "quote" => {
                        let len = expr.as_ref().list_len();
                        if len != 2 {
                            return Err(ValRef::symbol(String::from("quote requires 1 argument")));
                        }
                        let quoted = expr
                            .as_ref()
                            .list_nth(1)
                            .ok_or(ValRef::symbol(String::from("quote missing argument")))?;
                        return Ok(EvalResult::Done(quoted));
                    }
                    _ => {}
                }
            }

            let func = eval(car, env)?;

            let mut args = ValRef::nil();
            let mut current = cdr;
            loop {
                match current.as_ref() {
                    Value::Cons(arg_cell) => {
                        let (arg_car, arg_cdr) = arg_cell.borrow().clone();
                        let evaled = eval(arg_car, env)?;
                        args = ValRef::cons(evaled, args);
                        current = arg_cdr;
                    }
                    Value::Nil => break,
                    _ => return Err(ValRef::symbol(String::from("Malformed argument list"))),
                }
            }
            args = reverse_list(args);

            match func.as_ref() {
                Value::Builtin(f) => Ok(EvalResult::Done(f(&args)?)),
                Value::Lambda {
                    params,
                    body,
                    env: lambda_env,
                } => {
                    let param_count = params.as_ref().list_len();
                    let arg_count = args.as_ref().list_len();

                    if arg_count != param_count {
                        return Err(ValRef::symbol(String::from(
                            "Lambda argument count mismatch",
                        )));
                    }

                    let call_env = env_with_parent(lambda_env.clone());

                    let mut param_cur = params.clone();
                    let mut arg_cur = args.clone();

                    loop {
                        match (param_cur.as_ref(), arg_cur.as_ref()) {
                            (Value::Cons(p_cell), Value::Cons(a_cell)) => {
                                let (p_car, p_cdr) = p_cell.borrow().clone();
                                let (a_car, a_cdr) = a_cell.borrow().clone();
                                if let Value::Symbol(param_name) = p_car.as_ref() {
                                    env_set(&call_env, param_name.clone(), a_car);
                                }
                                param_cur = p_cdr;
                                arg_cur = a_cdr;
                            }
                            (Value::Nil, Value::Nil) => break,
                            _ => {
                                return Err(ValRef::symbol(String::from(
                                    "Parameter/argument mismatch",
                                )));
                            }
                        }
                    }

                    Ok(EvalResult::TailCall(body.clone(), call_env))
                }
                _ => Err(ValRef::symbol(String::from("Cannot call non-function"))),
            }
        }
        Value::Nil => Ok(EvalResult::Done(ValRef::nil())),
    }
}

pub fn eval(mut expr: ValRef, env: &ValRef) -> Result<ValRef, ValRef> {
    let mut current_env = env.clone();

    loop {
        match eval_step(expr, &current_env)? {
            EvalResult::Done(val) => return Ok(val),
            EvalResult::TailCall(new_expr, new_env) => {
                expr = new_expr;
                current_env = new_env;
            }
        }
    }
}

// ============================================================================
// Built-in Functions
// ============================================================================

fn builtin_add(args: &ValRef) -> Result<ValRef, ValRef> {
    let mut result: i64 = 0;
    let mut current = args.clone();

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (car, cdr) = cell.borrow().clone();
                let num = car
                    .as_number()
                    .ok_or(ValRef::symbol(String::from("+ requires numbers")))?;
                result = result
                    .checked_add(num)
                    .ok_or(ValRef::symbol(String::from("Integer overflow")))?;
                current = cdr;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid argument list"))),
        }
    }

    Ok(ValRef::number(result))
}

fn builtin_sub(args: &ValRef) -> Result<ValRef, ValRef> {
    let len = args.as_ref().list_len();
    if len == 0 {
        return Err(ValRef::symbol(String::from(
            "- requires at least 1 argument",
        )));
    }

    let first = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("- missing first argument")))?;
    let first_num = first
        .as_number()
        .ok_or(ValRef::symbol(String::from("- requires numbers")))?;

    if len == 1 {
        return Ok(ValRef::number(
            first_num
                .checked_neg()
                .ok_or(ValRef::symbol(String::from("Integer overflow")))?,
        ));
    }

    let mut result = first_num;
    let mut current = args.clone();
    if let Value::Cons(cell) = current.as_ref() {
        let (_, rest) = cell.borrow().clone();
        current = rest;
    }

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (car, cdr) = cell.borrow().clone();
                let num = car
                    .as_number()
                    .ok_or(ValRef::symbol(String::from("- requires numbers")))?;
                result = result
                    .checked_sub(num)
                    .ok_or(ValRef::symbol(String::from("Integer overflow")))?;
                current = cdr;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid argument list"))),
        }
    }

    Ok(ValRef::number(result))
}

fn builtin_mul(args: &ValRef) -> Result<ValRef, ValRef> {
    let mut result: i64 = 1;
    let mut current = args.clone();

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (car, cdr) = cell.borrow().clone();
                let num = car
                    .as_number()
                    .ok_or(ValRef::symbol(String::from("* requires numbers")))?;
                result = result
                    .checked_mul(num)
                    .ok_or(ValRef::symbol(String::from("Integer overflow")))?;
                current = cdr;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid argument list"))),
        }
    }

    Ok(ValRef::number(result))
}

fn builtin_div(args: &ValRef) -> Result<ValRef, ValRef> {
    let len = args.as_ref().list_len();
    if len < 2 {
        return Err(ValRef::symbol(String::from(
            "/ requires at least 2 arguments",
        )));
    }

    let first = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("/ missing first argument")))?;
    let mut result = first
        .as_number()
        .ok_or(ValRef::symbol(String::from("/ requires numbers")))?;

    let mut current = args.clone();
    if let Value::Cons(cell) = current.as_ref() {
        let (_, rest) = cell.borrow().clone();
        current = rest;
    }

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (car, cdr) = cell.borrow().clone();
                let num = car
                    .as_number()
                    .ok_or(ValRef::symbol(String::from("/ requires numbers")))?;
                if num == 0 {
                    return Err(ValRef::symbol(String::from("Division by zero")));
                }
                result = result
                    .checked_div(num)
                    .ok_or(ValRef::symbol(String::from("Integer overflow")))?;
                current = cdr;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid argument list"))),
        }
    }

    Ok(ValRef::number(result))
}

fn builtin_eq(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 2 {
        return Err(ValRef::symbol(String::from("= requires 2 arguments")));
    }
    let a = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("= missing arg 1")))?;
    let b = args
        .as_ref()
        .list_nth(1)
        .ok_or(ValRef::symbol(String::from("= missing arg 2")))?;
    let a_num = a
        .as_number()
        .ok_or(ValRef::symbol(String::from("= requires numbers")))?;
    let b_num = b
        .as_number()
        .ok_or(ValRef::symbol(String::from("= requires numbers")))?;
    Ok(ValRef::bool_val(a_num == b_num))
}

fn builtin_lt(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 2 {
        return Err(ValRef::symbol(String::from("< requires 2 arguments")));
    }
    let a = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("< missing arg 1")))?;
    let b = args
        .as_ref()
        .list_nth(1)
        .ok_or(ValRef::symbol(String::from("< missing arg 2")))?;
    let a_num = a
        .as_number()
        .ok_or(ValRef::symbol(String::from("< requires numbers")))?;
    let b_num = b
        .as_number()
        .ok_or(ValRef::symbol(String::from("< requires numbers")))?;
    Ok(ValRef::bool_val(a_num < b_num))
}

fn builtin_gt(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 2 {
        return Err(ValRef::symbol(String::from("> requires 2 arguments")));
    }
    let a = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("> missing arg 1")))?;
    let b = args
        .as_ref()
        .list_nth(1)
        .ok_or(ValRef::symbol(String::from("> missing arg 2")))?;
    let a_num = a
        .as_number()
        .ok_or(ValRef::symbol(String::from("> requires numbers")))?;
    let b_num = b
        .as_number()
        .ok_or(ValRef::symbol(String::from("> requires numbers")))?;
    Ok(ValRef::bool_val(a_num > b_num))
}

fn builtin_list(args: &ValRef) -> Result<ValRef, ValRef> {
    Ok(args.clone())
}

fn builtin_car(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("car requires 1 argument")));
    }
    let list = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("car missing argument")))?;
    let cell = list
        .as_cons()
        .ok_or(ValRef::symbol(String::from("car requires a cons/list")))?;
    let (car, _) = cell.borrow().clone();
    Ok(car)
}

fn builtin_cdr(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("cdr requires 1 argument")));
    }
    let list = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("cdr missing argument")))?;
    let cell = list
        .as_cons()
        .ok_or(ValRef::symbol(String::from("cdr requires a cons/list")))?;
    let (_, cdr) = cell.borrow().clone();
    Ok(cdr)
}

fn builtin_cons_fn(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 2 {
        return Err(ValRef::symbol(String::from("cons requires 2 arguments")));
    }
    let car = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("cons missing arg 1")))?;
    let cdr = args
        .as_ref()
        .list_nth(1)
        .ok_or(ValRef::symbol(String::from("cons missing arg 2")))?;
    Ok(ValRef::cons(car, cdr))
}

fn builtin_null(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("null? requires 1 argument")));
    }
    let val = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("null? missing argument")))?;
    Ok(ValRef::bool_val(val.is_nil()))
}

fn builtin_cons_p(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("cons? requires 1 argument")));
    }
    let val = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("cons? missing argument")))?;
    Ok(ValRef::bool_val(val.as_cons().is_some()))
}

fn builtin_length(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("length requires 1 argument")));
    }
    let list = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("length missing argument")))?;
    let len = list.as_ref().list_len();
    Ok(ValRef::number(len as i64))
}

fn builtin_append(args: &ValRef) -> Result<ValRef, ValRef> {
    let mut result = ValRef::nil();
    let mut current = args.clone();

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (list, rest) = cell.borrow().clone();
                let mut list_cur = list;
                loop {
                    match list_cur.as_ref() {
                        Value::Cons(item_cell) => {
                            let (item, item_rest) = item_cell.borrow().clone();
                            result = ValRef::cons(item, result);
                            list_cur = item_rest;
                        }
                        Value::Nil => break,
                        _ => break,
                    }
                }
                current = rest;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid argument list"))),
        }
    }

    Ok(reverse_list(result))
}

fn builtin_reverse(args: &ValRef) -> Result<ValRef, ValRef> {
    if args.as_ref().list_len() != 1 {
        return Err(ValRef::symbol(String::from("reverse requires 1 argument")));
    }
    let list = args
        .as_ref()
        .list_nth(0)
        .ok_or(ValRef::symbol(String::from("reverse missing argument")))?;
    Ok(reverse_list(list))
}

// ============================================================================
// Public API
// ============================================================================

pub fn eval_str(input: &str, env: &ValRef) -> Result<ValRef, ValRef> {
    let expr = parse(input)?;
    let result = eval(expr, env)?;
    Ok(result)
}

pub fn eval_str_multiple(input: &str, env: &ValRef) -> Result<ValRef, ValRef> {
    let expressions = parse_multiple(input)?;
    if expressions.is_nil() {
        return Err(ValRef::symbol(String::from("No expressions to evaluate")));
    }

    let mut last_result = ValRef::nil();
    let mut current = expressions;

    loop {
        match current.as_ref() {
            Value::Cons(cell) => {
                let (expr, rest) = cell.borrow().clone();
                last_result = eval(expr, env)?;
                current = rest;
            }
            Value::Nil => break,
            _ => return Err(ValRef::symbol(String::from("Invalid expression list"))),
        }
    }

    Ok(last_result)
}

impl PartialEq for ValRef {
    fn eq(&self, other: &Self) -> bool {
        match (self.as_ref(), other.as_ref()) {
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Char(a), Value::Char(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Nil, Value::Nil) => true,
            (Value::Cons(a_cell), Value::Cons(b_cell)) => {
                let (a_car, a_cdr) = a_cell.borrow().clone();
                let (b_car, b_cdr) = b_cell.borrow().clone();
                a_car == b_car && a_cdr == b_cdr
            }
            (Value::Builtin(a), Value::Builtin(b)) => core::ptr::eq(a as *const _, b as *const _),
            (
                Value::Lambda {
                    params: p1,
                    body: b1,
                    env: _,
                },
                Value::Lambda {
                    params: p2,
                    body: b2,
                    env: _,
                },
            ) => p1 == p2 && b1 == b2,
            _ => false,
        }
    }
}

pub fn new_env() -> ValRef {
    env_new()
}
