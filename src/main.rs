use std::collections::HashMap;
use std::fmt;
use std::io;
use std::io::Write;
use std::num::ParseFloatError;
use std::rc::Rc;

/*
  Types
*/

#[derive(Debug, Clone, PartialEq)]
enum RispExp {
    Bool(bool),
    Symbol(String),
    Number(f64),
    List(Vec<RispExp>),
    Func(fn(&[RispExp]) -> Result<RispExp, RispErr>),
    Lambda(RispLambda),
}

#[derive(Debug, Clone, PartialEq)]
struct RispLambda {
    params_exp: Rc<RispExp>,
    body_exp: Rc<RispExp>,
}

impl fmt::Display for RispExp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let str = match self {
            RispExp::Bool(a) => a.to_string(),
            RispExp::Symbol(s) => s.clone(),
            RispExp::Number(n) => n.to_string(),
            RispExp::List(list) => {
                let xs: Vec<String> = list.iter().map(|x| x.to_string()).collect();
                format!("({})", xs.join(","))
            }
            RispExp::Func(_) => "Function {}".to_string(),
            RispExp::Lambda(_) => "Lambda {}".to_string(),
        };

        write!(f, "{}", str)
    }
}

#[derive(Debug)]
enum RispErr {
    Reason(String),
}

#[derive(Debug, Clone)]
struct RispEnv<'a> {
    data: HashMap<String, RispExp>,
    outer: Option<&'a RispEnv<'a>>,
}

/*
  Parse
*/

fn tokenize(expr: String) -> Vec<String> {
    expr.replace('(', " ( ")
        .replace(')', " ) ")
        .split_whitespace()
        .map(|x| x.to_string())
        .collect()
}

fn parse(tokens: &[String]) -> Result<(RispExp, &[String]), RispErr> {
    let (token, rest) = tokens
        .split_first()
        .ok_or(RispErr::Reason("could not get token".to_string()))?;
    match &token[..] {
        "(" => read_seq(rest),
        ")" => Err(RispErr::Reason("unexpected `)`".to_string())),
        _ => Ok((parse_atom(token), rest)),
    }
}

fn read_seq(tokens: &[String]) -> Result<(RispExp, &[String]), RispErr> {
    let mut res: Vec<RispExp> = vec![];
    let mut xs = tokens;
    loop {
        let (next_token, rest) = xs
            .split_first()
            .ok_or(RispErr::Reason("could not find closing `)`".to_string()))?;
        if next_token == ")" {
            return Ok((RispExp::List(res), rest)); // skip `)`, head to the token after
        }
        let (exp, new_xs) = parse(xs)?;
        res.push(exp);
        xs = new_xs;
    }
}

fn parse_atom(token: &str) -> RispExp {
    match token {
        "true" => RispExp::Bool(true),
        "false" => RispExp::Bool(false),
        _ => {
            let potential_float: Result<f64, ParseFloatError> = token.parse();
            match potential_float {
                Ok(v) => RispExp::Number(v),
                Err(_) => RispExp::Symbol(token.to_string().clone()),
            }
        }
    }
}

/*
  Env
*/

macro_rules! ensure_tonicity {
    ($check_fn:expr) => {{
        |args: &[RispExp]| -> Result<RispExp, RispErr> {
            let floats = parse_list_of_floats(args)?;
            let first = floats
                .first()
                .ok_or(RispErr::Reason("expected at least one number".to_string()))?;
            let rest = &floats[1..];
            fn f(prev: &f64, xs: &[f64]) -> bool {
                match xs.first() {
                    Some(x) => $check_fn(prev, x) && f(x, &xs[1..]),
                    None => true,
                }
            }
            Ok(RispExp::Bool(f(first, rest)))
        }
    }};
}

impl Default for RispEnv<'_> {
    fn default() -> Self {
        let mut data: HashMap<String, RispExp> = HashMap::new();
        data.insert(
            "+".to_string(),
            RispExp::Func(|args: &[RispExp]| -> Result<RispExp, RispErr> {
                let floats = parse_list_of_floats(args)?;
                if floats.len() == 1 {
                    return Ok(RispExp::Number(floats[0].abs()));
                }

                let sum = floats.iter().fold(0.0, |sum, a| sum + a);

                Ok(RispExp::Number(sum))
            }),
        );
        data.insert(
            "-".to_string(),
            RispExp::Func(|args: &[RispExp]| -> Result<RispExp, RispErr> {
                let floats = parse_list_of_floats(args)?;
                if floats.len() == 1 {
                    return Ok(RispExp::Number(-1.0 * floats[0]));
                }

                let first = *floats
                    .first()
                    .ok_or(RispErr::Reason("expected at least one number".to_string()))?;
                let sum_of_rest = floats[1..].iter().fold(0.0, |sum, a| sum + a);

                Ok(RispExp::Number(first - sum_of_rest))
            }),
        );
        data.insert(
            "*".to_string(),
            RispExp::Func(|args: &[RispExp]| -> Result<RispExp, RispErr> {
                let floats = parse_list_of_floats(args)?;

                let rest = floats.iter().fold(1.0, |sum, a| sum * a);

                Ok(RispExp::Number(rest))
            }),
        );
        data.insert(
            "/".to_string(),
            RispExp::Func(|args: &[RispExp]| -> Result<RispExp, RispErr> {
                let floats = parse_list_of_floats(args)?;

                let mut total: f64 = *floats
                    .first()
                    .ok_or(RispErr::Reason("expected at least one number".to_string()))?;

                for float in &floats[1..] {
                    total /= float;
                }

                Ok(RispExp::Number(total))
            }),
        );
        data.insert(
            "=".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a == b)),
        );
        data.insert(
            ">".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a > b)),
        );
        data.insert(
            ">=".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a >= b)),
        );
        data.insert(
            "<".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a < b)),
        );
        data.insert(
            "<=".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a <= b)),
        );
        data.insert(
            "!=".to_string(),
            RispExp::Func(ensure_tonicity!(|a, b| a != b)),
        );

        RispEnv { data, outer: None }
    }
}

fn parse_list_of_floats(args: &[RispExp]) -> Result<Vec<f64>, RispErr> {
    args.iter().map(parse_single_float).collect()
}

fn parse_single_float(exp: &RispExp) -> Result<f64, RispErr> {
    match exp {
        RispExp::Number(num) => Ok(*num),
        _ => Err(RispErr::Reason("expected a number".to_string())),
    }
}

/*
  Eval
*/

fn eval_if_args(arg_forms: &[RispExp], env: &mut RispEnv) -> Result<RispExp, RispErr> {
    let test_form = arg_forms
        .first()
        .ok_or(RispErr::Reason("expected test form".to_string()))?;
    let test_eval = eval(test_form, env)?;
    match test_eval {
        RispExp::Bool(b) => {
            let form_idx = if b { 1 } else { 2 };
            let res_form = arg_forms
                .get(form_idx)
                .ok_or(RispErr::Reason(format!("expected form idx={}", form_idx)))?;

            eval(res_form, env)
        }
        _ => Err(RispErr::Reason(format!(
            "unexpected test form='{}'",
            test_form
        ))),
    }
}

fn eval_def_args(arg_forms: &[RispExp], env: &mut RispEnv) -> Result<RispExp, RispErr> {
    let first_form = arg_forms
        .first()
        .ok_or(RispErr::Reason("expected first form".to_string()))?;
    let first_str = match first_form {
        RispExp::Symbol(s) => Ok(s.clone()),
        _ => Err(RispErr::Reason(
            "expected first form to be a symbol".to_string(),
        )),
    }?;
    let second_form = arg_forms
        .get(1)
        .ok_or(RispErr::Reason("expected second form".to_string()))?;
    if arg_forms.len() > 2 {
        return Err(RispErr::Reason("def can only have two forms ".to_string()));
    }
    let second_eval = eval(second_form, env)?;
    env.data.insert(first_str, second_eval);

    Ok(first_form.clone())
}

fn eval_lambda_args(arg_forms: &[RispExp]) -> Result<RispExp, RispErr> {
    let params_exp = arg_forms
        .first()
        .ok_or(RispErr::Reason("expected args form".to_string()))?;
    let body_exp = arg_forms
        .get(1)
        .ok_or(RispErr::Reason("expected second form".to_string()))?;
    if arg_forms.len() > 2 {
        return Err(RispErr::Reason(
            "fn definition can only have two forms ".to_string(),
        ));
    }

    Ok(RispExp::Lambda(RispLambda {
        body_exp: Rc::new(body_exp.clone()),
        params_exp: Rc::new(params_exp.clone()),
    }))
}

fn eval_built_in_form(
    exp: &RispExp,
    arg_forms: &[RispExp],
    env: &mut RispEnv,
) -> Option<Result<RispExp, RispErr>> {
    match exp {
        RispExp::Symbol(s) => match s.as_ref() {
            "if" => Some(eval_if_args(arg_forms, env)),
            "def" => Some(eval_def_args(arg_forms, env)),
            "fn" => Some(eval_lambda_args(arg_forms)),
            _ => None,
        },
        _ => None,
    }
}

fn env_get(k: &str, env: &RispEnv) -> Option<RispExp> {
    match env.data.get(k) {
        Some(exp) => Some(exp.clone()),
        None => match &env.outer {
            Some(outer_env) => env_get(k, outer_env),
            None => None,
        },
    }
}

fn parse_list_of_symbol_strings(form: Rc<RispExp>) -> Result<Vec<String>, RispErr> {
    let list = match form.as_ref() {
        RispExp::List(s) => Ok(s.clone()),
        _ => Err(RispErr::Reason(
            "expected args form to be a list".to_string(),
        )),
    }?;
    list.iter()
        .map(|x| match x {
            RispExp::Symbol(s) => Ok(s.clone()),
            _ => Err(RispErr::Reason(
                "expected symbols in the argument list".to_string(),
            )),
        })
        .collect()
}

fn env_for_lambda<'a>(
    params: Rc<RispExp>,
    arg_forms: &[RispExp],
    outer_env: &'a mut RispEnv,
) -> Result<RispEnv<'a>, RispErr> {
    let ks = parse_list_of_symbol_strings(params)?;
    if ks.len() != arg_forms.len() {
        return Err(RispErr::Reason(format!(
            "expected {} arguments, got {}",
            ks.len(),
            arg_forms.len()
        )));
    }
    let vs = eval_forms(arg_forms, outer_env)?;
    let mut data: HashMap<String, RispExp> = HashMap::new();
    for (k, v) in ks.iter().zip(vs.iter()) {
        data.insert(k.clone(), v.clone());
    }
    Ok(RispEnv {
        data,
        outer: Some(outer_env),
    })
}

fn eval_forms(arg_forms: &[RispExp], env: &mut RispEnv) -> Result<Vec<RispExp>, RispErr> {
    arg_forms.iter().map(|x| eval(x, env)).collect()
}

fn eval(exp: &RispExp, env: &mut RispEnv) -> Result<RispExp, RispErr> {
    match exp {
        RispExp::Symbol(k) => {
            env_get(k, env).ok_or(RispErr::Reason(format!("unexpected symbol k='{}'", k)))
        }
        RispExp::Bool(_a) => Ok(exp.clone()),
        RispExp::Number(_a) => Ok(exp.clone()),
        RispExp::List(list) => {
            let first_form = list
                .first()
                .ok_or(RispErr::Reason("expected a non-empty list".to_string()))?;
            let arg_forms = &list[1..];
            match eval_built_in_form(first_form, arg_forms, env) {
                Some(res) => res,
                None => {
                    let first_eval = eval(first_form, env)?;
                    match first_eval {
                        RispExp::Func(f) => f(&eval_forms(arg_forms, env)?),
                        RispExp::Lambda(lambda) => {
                            let new_env = &mut env_for_lambda(lambda.params_exp, arg_forms, env)?;
                            eval(&lambda.body_exp, new_env)
                        }
                        _ => Err(RispErr::Reason("first form must be a function".to_string())),
                    }
                }
            }
        }
        RispExp::Func(_) => Err(RispErr::Reason("unexpected form".to_string())),
        RispExp::Lambda(_) => Err(RispErr::Reason("unexpected form".to_string())),
    }
}

/*
  Repl
*/

fn parse_eval(expr: String, env: &mut RispEnv) -> Result<RispExp, RispErr> {
    let (parsed_exp, _) = parse(&tokenize(expr))?;
    let evaled_exp = eval(&parsed_exp, env)?;

    Ok(evaled_exp)
}

fn slurp_expr() -> String {
    let mut expr = String::new();

    io::stdin()
        .read_line(&mut expr)
        .expect("Failed to read line");

    expr
}

fn repl(env: &mut RispEnv) {
    loop {
        print!("risp> ");
        let _ = io::stdout().flush();
        let expr = slurp_expr();
        interpret(expr, env);
    }
}

fn interpret(program: String, env: &mut RispEnv) {
    for line in program.lines() {
        match parse_eval(line.to_string(), env) {
            Ok(res) => println!("// 🔥 => {}", res),
            Err(e) => match e {
                RispErr::Reason(msg) => println!("// 🙀 => {}", msg),
            },
        }
    }
}

fn write_executable(expr: RispExp, file_name: Option<&str>) {
    use std::fs::File;

    let mut f = match file_name {
        Some(name) => File::options().create(true).write(true).open(name).unwrap(),
        None => File::options()
            .create(true)
            .write(true)
            .open("tmp.s")
            .unwrap(),
    };

    let expr_num = match expr {
        RispExp::Bool(true) => ExprNum::Unsigned(1),
        RispExp::Bool(false) => ExprNum::Unsigned(0),
        RispExp::Number(n) => {
            if n.fract() == 0.0 {
                ExprNum::Unsigned(n as u64)
            } else {
                let bits = n.to_bits();
                let high = (bits >> 32) as u32;
                let low = bits as u32;

                ExprNum::Float(low, high)
            }
        }
        RispExp::Symbol(_) | RispExp::List(_) | RispExp::Func(_) | RispExp::Lambda(_) => {
            unreachable!()
        }
    };

    enum ExprNum {
        Float(u32, u32),
        Unsigned(u64),
    }

    let program = match expr_num {
        ExprNum::Float(low, high) => {
            #[cfg(all(
                target_arch = "x86_64",
                any(target_os = "linux", target_os = "android")
            ))]
            format!(
                r#".LC1:
        .string "%f\n"
        .globl main
main:
        subq    $8, %rsp
        movl    $.LC1, %edi
        movl    $1, %eax
        movsd   .LC0(%rip), %xmm0
        call    printf
        xorl    %eax, %eax
        addq    $8, %rsp
        ret
.LC0:
        .long   {}
        .long   {}
"#,
                low, high
            )
        }
        ExprNum::Unsigned(num) => {
            #[cfg(all(
                target_arch = "x86_64",
                any(target_os = "linux", target_os = "android")
            ))]
            format!(
                r#".LC0:
        .string "%lu\n"
        .globl main
main:
        subq    $8, %rsp
        movq    ${}, %rsi
        movl    $.LC0, %edi
        xorl    %eax, %eax
        call    printf
        xorl    %eax, %eax
        addq    $8, %rsp
        ret
"#,
                num
            )
        }
    };

    f.write_all(program.as_bytes()).unwrap();
}

fn compile_eval(program: String, env: &mut RispEnv) -> Result<(), RispErr> {
    let mut evaled_exp = RispExp::Bool(true);
    for line in program.lines() {
        match parse_eval(line.to_string(), env) {
            Ok(res) => evaled_exp = res,
            Err(e) => match e {
                RispErr::Reason(msg) => panic!("// 🙀 => {}", msg),
            },
        }
    }

    write_executable(evaled_exp, None);

    Ok(())
}

fn main() {
    use std::env::args;
    use std::fs::read_to_string;

    let arguments: Vec<_> = args().collect();
    let mut env = RispEnv::default();

    match arguments.len() {
        1 => repl(&mut env),
        2 => {
            let program = read_to_string(arguments[1].clone()).unwrap();
            interpret(program, &mut env);
        }
        3 => {
            let program = read_to_string(arguments[1].clone()).unwrap();
            let _ = compile_eval(program, &mut env);
        }
        _ => eprintln!("Only takes up to three arguments"),
    }
}
