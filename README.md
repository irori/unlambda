# Unlambda interpreter

This is a fast and memory-efficient interpreter of the [Unlambda](http://www.madore.org/~david/programs/unlambda/) programming language.

## Features

- Generational garbage collection
- Internally substitutes terms of some patterns, so that they evaluate faster and use less memory. The following substitution rules are implemented:

```
     `S`Kf -> `Bf    where ```Bfgx = `f`gx
   ``Sf`Kg -> ``Cfg  where ```Cfgx = ``fxg
   ``SI`Kx -> `Tx    where   ``Txy = `yx
 ``S`Tx`Ky -> ``Vxy  where ```Vxyz = ``zxy
```

## Usage

```sh
$ unlambda [-v[0-3]] [program-file]
```

If _program-file_ is not specified, Unlambda program is read from the standard input.

The `-v[0-3]` option sets the verbosity level.

- `-v0` (default): Do not print any debug information.
- `-v1`: Print some statistics after execution.
- `-v2`: Print logs for major GCs.
- `-v3`: Print logs for minor GCs.

## License

MIT
