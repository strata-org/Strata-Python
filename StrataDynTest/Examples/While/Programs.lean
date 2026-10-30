/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Elab
public import StrataDyn.Examples.While.Run

set_option autoImplicit false

/-!
# While programs

The example programs, in the While dialect's syntax between `#while` and `#end`, and
`examples`, the runs that `RunTest.lean` checks: a program, its entry function and arguments,
and the outcome as `showOutcome` prints it.
-/

namespace Strata.Dyn.While.Programs

open Strata.Dyn.While.Ast

@[expose] public section

/-! ## Programs -/

def arith : Program := #while
  fun main() : Int { return (7 + 3) * 4 - 10 / 3; }
#end

def sum : Program := #while
  fun sum(n : Int) : Int {
    var s : Int := 0;
    var i : Int := 1;
    while (i <= n) { s := s + i; i := i + 1; }
    return s;
  }
#end

def gcd : Program := #while
  fun gcd(a : Int, b : Int) : Int {
    while (b != 0) { var t : Int := a % b; a := b; b := t; }
    return a;
  }
#end

def fact : Program := #while
  fun fact(n : Int) : Int {
    var r : Int := 1;
    while (n > 1) { r := r * n; n := n - 1; }
    return r;
  }
#end

def fib : Program := #while
  fun fib(n : Int) : Int {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
  }
#end

/-- Lists: build, measure, sum and reverse. -/
def lists : Program := #while
  fun range(n : Int) : IntList {
    var l : IntList := nil;
    while (n > 0) { l := n :: l; n := n - 1; }
    return l;
  }
  fun length(l : IntList) : Int {
    return case l of nil => 0 | h :: t => 1 + length(t);
  }
  fun total(l : IntList) : Int {
    return case l of nil => 0 | h :: t => h + total(t);
  }
  fun revOnto(l : IntList, acc : IntList) : IntList {
    return case l of nil => acc | h :: t => revOnto(t, h :: acc);
  }
  fun lengthOfRange(n : Int) : Int { return length(range(n)); }
  fun totalOfRange(n : Int) : Int { return total(range(n)); }
  fun reverseRange(n : Int) : IntList { return revOnto(range(n), nil); }
  fun headOr(n : Int, d : Int) : Int {
    return case range(n) of nil => d | h :: t => h;
  }
#end

/-- Raising and catching: a handler in the same function, and one in a caller. -/
def exceptions : Program := #while
  fun safeDiv(a : Int, b : Int) : Int {
    try { return a / b; } catch e => { return 0 - e; }
  }
  fun check(x : Int) : Int {
    if (x < 0) { raise 42; }
    return x;
  }
  fun viaCall(x : Int) : Int {
    var y : Int := 0;
    try { y := check(x) + 1; } catch e => { y := e; }
    return y;
  }
  fun boom(x : Int) : Int { return x / 0; }
  fun nested(x : Int) : Int {
    var r : Int := 0;
    try {
      try { r := 10 / x; } catch e => { raise e + 100; }
    } catch e => { r := e; }
    return r;
  }
#end

def spin : Program := #while
  fun spin() : Int { while (true) { } return 0; }
#end

/-- Uses `^`, which lowers to `while.pow`, whose rule is a `semanticGap`. -/
def power : Program := #while
  fun cube(x : Int) : Int { return x ^ 3; }
#end

/-- A loop of `n` iterations, for benchmarks. -/
def loop : Program := #while
  fun loop(n : Int) : Int {
    var i : Int := 0;
    while (i < n) { i := i + 1; }
    return i;
  }
#end

/-- A loop of `n` calls, for benchmarks. -/
def calls : Program := #while
  fun inc(x : Int) : Int { return x + 1; }
  fun calls(n : Int) : Int {
    var i : Int := 0;
    while (i < n) { i := inc(i); }
    return i;
  }
#end

/-- Cells: a counter, a cell written by its callee, aliases, and a list built in a cell. -/
def cells : Program := #while
  fun counter(n : Int) : Int {
    var c : Ref := ref 0;
    while (*c < n) { *c := *c + 1; }
    return *c;
  }
  fun bump(c : Ref, k : Int) : Unit { *c := *c + k; }
  fun escape(n : Int) : Int {
    var c : Ref := ref n;
    bump(c, 5);
    bump(c, 10);
    return *c;
  }
  fun alias(n : Int) : Int {
    var a : Ref := ref n;
    var b : Ref := a;
    *b := *b * 2;
    return *a;
  }
  fun cell(x : Int) : Ref { return ref x; }
  fun two(n : Int) : Int {
    var a : Ref := cell(n);
    var b : Ref := cell(n + 1);
    *a := *a + *b;
    return *a * 10 + *b;
  }
  fun push(s : ListRef, x : Int) : Unit { *s := x :: *s; }
  fun stack(n : Int) : IntList {
    var s : ListRef := ref nil;
    var i : Int := 0;
    while (i < n) { push(s, i); i := i + 1; }
    return *s;
  }
#end

/-! ### Regions

Loops and branches whose bodies are regions of the operation, with their effects in cells. -/

/-- `counter` with a `region while`. -/
def rcounter : Program := #while
  fun rcounter(n : Int) : Int {
    var c : Ref := ref 0;
    region while (*c < n) { *c := *c + 1; }
    return *c;
  }
#end

/-- Regions three deep: two loops and a branch. -/
def rnested : Program := #while
  fun nested(n : Int) : Int {
    var s : Ref := ref 0;
    var i : Ref := ref 0;
    region while (*i < n) {
      var j : Ref := ref 0;
      region while (*j < n) {
        region if (*i == *j) { *s := *s + 100; } else { *s := *s + *i * *j; }
        *j := *j + 1;
      }
      *i := *i + 1;
    }
    return *s;
  }
#end

/-- A region that reaches `while.pow`'s gap. -/
def rgap : Program := #while
  fun rgap(x : Int) : Int {
    var c : Ref := ref x;
    region if (x > 0) { *c := *c ^ 2; }
    return *c;
  }
#end

/-- A region that runs out of fuel. -/
def rspin : Program := #while
  fun rspin() : Int { region while (true) { } return 0; }
#end

/-- An exception raised and caught inside a region. -/
def rcatch : Program := #while
  fun rcatch(n : Int) : Int {
    var c : Ref := ref 0;
    var i : Ref := ref 0;
    region while (*i < n) {
      try { *c := *c + 10 / (*i - 2); } catch e => { *c := *c + 1000; }
      *i := *i + 1;
    }
    return *c;
  }
#end

/-- An exception that leaves a region as a `Flow`, which `while.loop` raises along its `^err`,
to a handler outside the loop. -/
def rescape : Program := #while
  fun rescape(n : Int) : Int {
    var c : Ref := ref 0;
    try {
      region while (true) {
        *c := *c + 1;
        if (*c == n) { raise *c * 7; }
      }
    } catch e => { return e; }
    return 0;
  }
#end

/-- The world: `print` appends to Base's output, inside a region too, and `tick` counts in
While's part. -/
def logged : Program := #while
  fun logged(n : Int) : Int {
    var c : Ref := ref 0;
    region while (*c < n) { print(*c * 10); *c := *c + 1; }
    print(tick());
    return tick() + tick();
  }
#end

/-- `counter` with a `Cell`, which rules make, read and write on the machine's heap. -/
def wcells : Program := #while
  fun wcounter(n : Int) : Int {
    var c : Cell := wcell(0);
    while (*c < n) { *c := *c + 1; }
    return *c;
  }
#end

/-- The oracle: `n` bits, each chosen by `pick(1)`, most significant first. -/
def coins : Program := #while
  fun coins(n : Int) : Int {
    var c : Ref := ref 0;
    var s : Ref := ref 0;
    region while (*c < n) { *s := *s * 2 + pick(1); *c := *c + 1; }
    return *s;
  }
#end



/-! ## The example set -/

/-- An example: a program, its entry function and arguments, and its expected outcome. -/
structure Example where
  name : String
  prog : Program
  entry : String
  args : Array Int
  expected : String

def examples : List Example := [
  ⟨"arith", arith, "main", #[], "ok 37"⟩,
  ⟨"sum 100", sum, "sum", #[100], "ok 5050"⟩,
  ⟨"gcd 12 18", gcd, "gcd", #[12, 18], "ok 6"⟩,
  ⟨"gcd 1071 462", gcd, "gcd", #[1071, 462], "ok 21"⟩,
  ⟨"fact 20", fact, "fact", #[20], "ok 2432902008176640000"⟩,
  ⟨"fib 15", fib, "fib", #[15], "ok 610"⟩,
  ⟨"length (range 10)", lists, "lengthOfRange", #[10], "ok 10"⟩,
  ⟨"total (range 100)", lists, "totalOfRange", #[100], "ok 5050"⟩,
  ⟨"reverse (range 4)", lists, "reverseRange", #[4], "ok 4 :: 3 :: 2 :: 1 :: nil"⟩,
  ⟨"head (range 0) or 7", lists, "headOr", #[0, 7], "ok 7"⟩,
  ⟨"safeDiv 7 2", exceptions, "safeDiv", #[7, 2], "ok 3"⟩,
  ⟨"safeDiv 7 0", exceptions, "safeDiv", #[7, 0], "ok -1"⟩,
  ⟨"viaCall 5", exceptions, "viaCall", #[5], "ok 6"⟩,
  ⟨"viaCall -1", exceptions, "viaCall", #[-1], "ok 42"⟩,
  ⟨"nested 0", exceptions, "nested", #[0], "ok 101"⟩,
  ⟨"boom 1", exceptions, "boom", #[1], "raised 1"⟩,
  ⟨"spin", spin, "spin", #[], "fault out of fuel"⟩,
  ⟨"cube 2", power, "cube", #[2], "fault gap: while.pow: not implemented"⟩,
  ⟨"counter 10", cells, "counter", #[10], "ok 10"⟩,
  ⟨"escape 1", cells, "escape", #[1], "ok 16"⟩,
  ⟨"alias 21", cells, "alias", #[21], "ok 42"⟩,
  ⟨"two 3", cells, "two", #[3], "ok 74"⟩,
  ⟨"stack 3", cells, "stack", #[3], "ok 2 :: 1 :: 0 :: nil"⟩,
  ⟨"rcounter 10", rcounter, "rcounter", #[10], "ok 10"⟩,
  ⟨"nested 3", rnested, "nested", #[3], "ok 304"⟩,
  ⟨"rgap 2", rgap, "rgap", #[2], "fault gap: while.pow: not implemented"⟩,
  ⟨"rgap -1", rgap, "rgap", #[-1], "ok -1"⟩,
  ⟨"rspin", rspin, "rspin", #[], "fault out of fuel"⟩,
  ⟨"rcatch 5", rcatch, "rcatch", #[5], "ok 1000"⟩,
  ⟨"rescape 3", rescape, "rescape", #[3], "ok 21"⟩,
  ⟨"logged 3", logged, "logged", #[3], "ok 5"⟩,
  ⟨"coins 3", coins, "coins", #[3], "ok 0"⟩,
  ⟨"wcounter 7", wcells, "wcounter", #[7], "ok 7"⟩]

end

end Strata.Dyn.While.Programs
