# Compiler for Ltac2

This Coq plugin provides a command `Ltac2 Compile tacs` which compiles
the given Ltac2 definitions using OCaml.

This provides large speedups (time divided by 4 or more) in
computation heavy tasks (tasks which mostly spend their time in
OCaml-implemented tactics are not affected).

See eg https://gitlab.com/coq/coq/-/jobs/4444514347 (significant fixes and optimizations have happened since that bench).

# Usage

Load the plugin, then call `Ltac2 Compile` on the tactics you care about, for instance:

``` coq
Ltac2 Compile Array.get Array.set.
```

Evaluation will then use the compiled code instead of the Ltac2 interpreter for these tactics.

`Print Ltac2` indicates whether a given tactic has been compiled.

# Dependency handling

By default the dependencies (eg `Array.iter_aux`) are also compiled.
If a dependency is a mutable tactic
This can be disabled with the attribute `#[recursive=no]`.

The attribute is provided for testing and debugging purposes. Users
should note that when disabling the automatic dependency inference,
providing the tactics in dependency order provides significantly
better performance (eg `Ltac2 Compile Array.iter_aux Array.iter` is
better than the opposite order).

# Limitations

## Compilation is local

Compilation is local to the current module or section. This means
compilation cannot be shared between `.v` files.

Workers (async proofs, `par:`) do not use the compilation results.

This limitation should eventually be lifted.

## No mutables

Mutable tactics cannot be compiled. In recursive mode if a dependency
is mutable its compilation is skipped and warning
`tac2compile-skipped-mutable` is emitted (its dependencies are still
compiled).

This limitation may be expected to be permanent.

## Quotations use the full Ltac2 environment

Quotations such as `constr:()` do not analyze their free variables, so
they need the entire Ltac2 environment. This may prevent GC or cause
slowness in large environments. This can be worked around using a side definition: instead of

``` coq
Ltac2 footac many things x y z := stuff constr:(foo $x).
```

do

``` coq
Ltac2 footac_aux x := constr:(foo $x).
Ltac2 footac many things x y z := stuff (footac_aux x).
```

The quotation in `footac_aux` does not need to be analyzed to know
that it only has access to `x`.

There are no plans to lift this limitation currently, but it may be
done if there are compelling cases (currently the performance impact
of needing the entire environment is unknown).

## No backtraces

The `Ltac2 Backtrace` and `Ltac Profiling` options are ignored by
compiled tactics, so backtraces and profiles will be incomplete when
using compilation.

This limitation will be lifted.

## String and open constructor patterns are suboptimal

The compilation of matches using string patterns or open constructor
patterns may show exponential behaviour when combined with deep
patterns or "or" (`|`) patterns.

Even shallow matches are linear whereas the interpreted mode is
logarithmic. As such matching over many specific open constructor (eg
errors) should be avoided.

There are no plans to lift this limitation currently. Lifting it for
shallow matches of open constructors could be done if there is a
compelling case (it's not clear how many constructors need to be
matched on before there is a noticeable impact).

# Roadmap (in no particular order)

- identify and implement further optimizations

- share compilation across files

- handle backtraces

- JIT evaluator (instead of using the interpreter, compile the given
  expression and run the result)?
  Bench https://gitlab.com/SkySkimmer/coq/-/jobs/5159008108 was not very promising,
  consider again once ahead of time compilation is done.
