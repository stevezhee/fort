# fort

This is pre-alpha stuff.  Most of it doesn't work.  Caveat emptor.

Some random stuff about fort:
  - type-safe, compiled
  - examples are in `test/*.fort`
  - types are sized, e.g. `/signed 64` is a signed 64-bit integer
  - comments begin with a `;;` and go to the end of the line
  - reserved words begin with a `/`, e.g. `/record`
  - the list of reserved words can be found in `src/Parser.hs`
  - indentation is used instead of braces/semicolons
  - dashes are allowed in variable names, e.g. `less-than`
  - all user defined operators have a corresponding function name, e.g. `< = less-than`
  - tupling is used instead of currying
  - a "tuple sections" like syntax is provided, e.g. `squared: Int -> Int = powi (,2)`
  - type signatures are specified after a `:`, e.g. `x: Int`
  - type signatures can be added most everywhere
  - `/if`s are multi-way ifs
  - the syntax is designed to be "low friction", i.e. cutting/pasting/naming expressions should work without extra syntax
  - top level declarations can have any order

# Dependency/Installation help
## llvm/llvm-hs
We're targeting llvm 7
### OSX
```
brew install llvm-hs/llvm/llvm-7.0
brew install stack
```
