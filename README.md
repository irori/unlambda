# Unlambda interpreter

A fast interpreter of the [Unlambda](http://www.madore.org/~david/programs/unlambda/) programming language.

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
