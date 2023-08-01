#!/bin/bash

export RUST_BACKTRACE=1

assert() {
  expected="$1"
  input="$2"

  echo "$input" > tmp.lisp

  ./target/debug/rispy tmp.lisp compile > tmp.s || exit
  gcc -static -o tmp tmp.s -z execstack
  actual=$(./tmp)

  if [ "$actual" = "$expected" ]; then
    echo "$input => $actual"
  else
    echo "$input => $expected expected, but got $actual"
    exit 1
  fi
}

cargo build

assert 0 0
assert 42 42
assert 21 '(- (+ 5 20) 4)'
assert 41 '(- (+ 12 34) 5)'
assert 47 '(+ (* 6 7) 5)'
assert 15 '(* (- 9 6) 5)'
assert 4  '(/ (+ 3 5) 2)'
assert 10 '(- (- 10 20))'
assert 10 '(- (- 10))'
assert 10 '(- (- (+ 10)))'

assert 0 '(= 0 1)'
assert 1 '(= 42 42)'
assert 1 '(!= 0 1)'
assert 0 '(!= 42 42)'

assert 1 '(< 0 1)'
assert 0 '(< 1 1)'
assert 0 '(< 2 1)'
assert 1 '(<= 0 1)'
assert 1 '(<= 1 1)'
assert 0 '(<= 2 1)'

assert 1 '(> 1 0)'
assert 0 '(> 1 1)'
assert 0 '(> 1 2)'
assert 1 '(>= 1 0)'
assert 1 '(>= 1 1)'
assert 0 '(>= 1 2)'

rm -f tmp.lisp tmp.res tmp.s tmp

echo OK
