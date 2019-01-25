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
  - one element "string" literals are of type Char, e.g. `"c": Char`

# Dependency/Installation help
## llvm/llvm-hs
We're targeting llvm 6
### OSX
Can easily get this via [a custom homebrew tap](https://github.com/llvm-hs/homebrew-llvm).
```
brew tap llvm-hs/llvm
brew install llvm-hs/llvm/llvm-6.0 --verbose
brew install stack
```
This will take a while, go walk your dog a few times...

Now, once it's installed, you'll have symlinks in `/usr/local/bin`, but they'll all be suffixed with `-6.0`. This doesn't play too nicely when tooling looks for i.e. `llc` instead of `llc-6.0`
Therefore, I profer an alternate workaround:
```
cp -R /usr/local/Cellar/llvm-6.0/6.0.1/{bin,bin-no-suffix}
export LLVM_DIR=/usr/local/Cellar/llvm-6.0/6.0.1/bin-no-suffix
for f in $(ls -1 $LLVM_DIR) ; do mv $LLVM_DIR/$f "${LLVM_DIR}/${f/-6.0}"; done
echo '# llvm 6 tooling' >> ~/.bash_profile
echo 'export PATH="${PATH}:/usr/local/Cellar/llvm-6.0/6.0.1/bin-no-suffix"' >> ~/.bash_profile
echo 'export LDFLAGS="$LDFLAGS -L/usr/local/opt/llvm-6.0/lib/llvm-6.0/lib"' >> ~/.bash_profile
source ~/.bash_profile
```
