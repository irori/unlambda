# Unlambda interpreter

This is a fast and memory-efficient interpreter of the
[Unlambda](http://www.madore.org/~david/programs/unlambda/) programming
language.

## Performance

Compared to [unl.c](http://users.math.cas.cz/~jerabek/ptakoviny/index.html#unl)
by Emil Jeřábek, which itself is 50-100 times faster than the official c-refcnt
interpreter, this interpreter is about 2 times faster and uses about 1/2 of
the memory.

| Benchmark     | unl.c | This interpreter |
|---------------|-------|------------------|
| adventure[^1] | 0.72s |   0.41s          |
| lisp[^2]      | 2.05s |   1.28s          |
| elvm-8cc[^3]  | 44.3s |   20.1s          |

[^1]: Complete [Adventure](https://github.com/irori/advent-unlambda) with the highest score (350 points).
[^2]: Compute `(fib 16)` in [Unlambda Lisp](https://github.com/irori/unlambda-lisp).
[^3]: Compile a [simple C program](https://github.com/shinh/elvm/blob/master/test/8cc.in) with `8cc.c.eir.unl` generated by [ELVM](https://github.com/shinh/elvm/) (`make unl`).

### Combinator Substitution

To achieve this performance, this interpreter introduces several new
combinators (`B`, `C`, `T`, and `V`) used only internally to substitute
expressions under evaluation by pattern matching. The following substitution
rules are implemented:

```
     `S`Kf -> `Bf    where ```Bfgx = `f`gx
   ``Sf`Kg -> ``Cfg  where ```Cfgx = ``fxg
   ``SI`Kx -> `Tx    where   ``Txy = `yx
 ``S`Tx`Ky -> ``Vxy  where ```Vxyz = ``zxy
```

(Note that `V` is the "pair" combinator (also known as "cons") and unrelated to
the Unlambda's `v` ("black hole" function) builtin.)

For example, when the first argument is given to `S`, if it is a partial
application of `K` (with one argument `f` given), it is replaced by `` `Bf``.

These auxiliary combinators use less memory and evaluate faster than the
original SKI-only combinator expressions.

### Garbage Collection

The object graph of Unlambda execution does not cycle, so memory management
can be done using reference counting. In fact, the c-refcnt interpreter and
unl.c both use reference counting.

However, since Unlambda frequently creates and destroys objects, reference
counting can be quite an overhead. Also, optimizing things like omitting
reference counter operations where possible, or overwriting and reusing objects
when the counter is 1, as unl.c does, can make the code more complicated.

Therefore, this interpreter adopted a generational garbage collector. For new
generation it uses two regions for 256k objects and performs copying GC.
Objects that have survived this minor GC twice are moved to the old generation
region. When the old generation area is full, a mark-sweep GC is performed on
the entire heap as a major GC.

Generational GC is very effective in Unlambda, often collecting more than 99%
of objects in minor GC. In benchmark measurements, GC accounted for about 1% of
the overall execution time.

In general, Generational GC requires a write barrier to keep track of
references from the old generation area to the new generation area. But in this
interpreter, once an object is created, it is never rewritten, so references
from the old generation to the new generation do not occur. Since no write
barrier is needed, the evaluator can be written without worrying too much
about GC (although copy GC changes object addresses).

## Building

```sh
$ make
```

## Usage

```sh
$ unlambda [options] [program-file]
```

If _program-file_ is not specified, Unlambda program is read from the standard input.

Options:

- `-h`: Print help and exit.
- `-v`: Print version and exit.
- `-v0` (default): Do not print any debug information.
- `-v1`: Print some statistics after execution.
- `-v2`: Print logs for major GCs.
- `-v3`: Print logs for minor GCs.

## License

This software is released under the [MIT License](LICENSE).
