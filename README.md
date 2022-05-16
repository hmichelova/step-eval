# step-eval

Tool for the step-by-step evaluation of basic Haskell expressions. 

## Prerequisities

- `GHC` in version 9.2.1
- `template-haskell` in version 2.18.0.0
- `hint` in version 0.9.0.5
- `transformers` in version 0.5.6.2 or newer
- `containers` in version 0.6.5.1

## Usage

Load the project to `GHCi` and set `TemplateHaskell` extension:

```bash
$ ghci -XTemplaceHaskell step-eval.hs
```

For evaluation of expression use function `evaluateExp` and the only argument is typed quoted expression. For instance `evaluateExp [|| map id [1, 2] ||]`

```haskell
ghci> evaluateExp [|| map id [1, 2] ||]
  map id [1, 2]

  Next action [N,a,q,h]? h
  ghc-step-eval help: 
    n: print next step and ask again
    a: print all following steps
    q: quit the evaluation
    h: print help

  Next action [N,a,q,h]? n
  id 1 : map id [2]

  Next action [N,a,q,h]? 
  1 : map id [2]

  Next action [N,a,q,h]? a
  1 : (id 2 : map id [])
  
  1 : (2 : map id [])
  
  1 : (2 : [])
  
  1 : [2]
  
  [1, 2]

  Expression is fully evaluated.
```
