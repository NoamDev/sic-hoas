type Term:
  Lam {f: Term -> Term}
  App {fun: Term, arg: Term}
  Sup {a: Term, b: Term}
  Cln {get: u24 -> Term}
  Var {idx: String}
  Open {term: Term}
  Era

# u24 here is used as bool
LazyDuplicate: u24 -> u24 -> Term -> (Term, Term)
(LazyDuplicate 0 0 x) = 
  let * = (Erase x)
  (Term/Era, Term/Era)
(LazyDuplicate _ _ x) = (Duplicate x)

# Duplicate: Term -> (Term, Term)
(Duplicate Term/Era) = (Term/Era, Term/Era)

(Duplicate (Term/Lam f)) =
  let (a, b) = (DUP (f (Term/Sup $x0 $x1)))
  (
    (Term/Lam λ$x0 a),
    (Term/Lam λ$x1 b)
  )

(Duplicate (Term/Sup fst snd)) =
  (fst, snd)

(Duplicate (Term/Var idx)) = 
  (
    (Term/Var idx),
    (Term/Var idx)
  )

(Duplicate (Term/Open x)) = 
  let (x0, x1) = (DUP x)
  (
    (Term/Open x0),
    (Term/Open x1)
  )

(Duplicate (Term/App fun arg)) = 
  let (x0, x1) = (DUP (Apply fun arg))
  (
    (Term/Open x0),
    (Term/Open x1)
  )

  (Duplicate (Term/Cln get)) = 
  let (x0, x1) = (DUP (get 1))
  (
    (Term/Open x0),
    (Term/Open x1)
  )

(DUP x) =
  let ($x0, $x1) = (LazyDuplicate $b0 $b1 x)
  (
    (Term/Cln λ$b0 $x0),
    (Term/Cln λ$b1 $x1)
  )

Normal: Term -> Term
(Normal (Term/Lam f)) = (Term/Lam λx (Normal (f (Term/Open x))))
(Normal (Term/App fun arg)) = (Normal (Apply fun arg))
(Normal (Term/Var idx)) = (Term/Var idx)
(Normal (Term/Open x)) = x
(Normal Term/Era) = Term/Era
(Normal (Term/Sup fst snd)) = (Term/Sup (Normal fst) (Normal snd))
(Normal (Term/Cln get)) = (Normal (get 1))

Apply: Term -> Term -> Term
(Apply (Term/Lam f) arg) = (f arg)
(Apply (Term/Var idx) arg) = (Term/App (Term/Var idx) (Normal arg))
(Apply (Term/App fun arg1) arg2) = (Apply (Apply fun arg1) arg2) 
(Apply (Term/Sup fst snd) arg) = 
  let (x0, x1) = (DUP arg)
  (Term/Sup (Apply fst x0) (Apply snd x1))
(Apply (Term/Cln get) arg) = (Apply (get 1) arg)
(Apply (Term/Open x) arg) = (Term/Open (Term/App x (Normal arg)))
(Apply Term/Era arg) =
  let * = (Erase arg)
  Term/Era

Erase: Term -> None
(Erase Term/Era) = *
(Erase (Term/App fun arg)) =
  let * = (Erase fun)
  let * = (Erase arg)
  *

(Erase (Term/Lam f)) = (Erase (f Term/Era))
(Erase (Term/Var idx)) = *
(Erase (Term/Open x)) = (Erase x)
(Erase (Term/Sup fst snd)) = 
  let * = (Erase fst)
  let * = (Erase snd)
  *
(Erase (Term/Cln get)) = (Erase (get 0))

## SHOWING

# This part is mostly stolen from https://github.com/FranchuFranchu/inet-hoas

# Paths are used for naming variables
type Bits = (I ~v) | (O ~v) | E

def Bits/to_u60(value: Bits) -> u24:
  fold value:
    case Bits/O:
      return value.v * 2
    case Bits/I:
      return value.v * 2 + 1
    case Bits/E:
      return 1

def U60/to_string(n: u24) -> String:
  if n < 10:
    return String/Cons('0' + n, String/Nil)
  else:
    return String/Cons('0' + n % 10, U60/to_string(n / 10))


(String/concat (String/Cons head tail) other) = (String/Cons head (String/concat tail other))
(String/concat String/Nil other) = other

(List/join List/Nil)         = ""
(List/join (List/Cons x xs)) = (String/concat x (List/join xs))

Show: Term -> Bits -> String
(Show (Term/Lam f) path) = 
  let var_id = (U60/to_string (Bits/to_u60 path))
  (List/join [
    "(λ"
    var_id
    "."
    (Show (f (Term/Var var_id)) (Bits/O path))
    ")"
  ])

(Show (Term/App x y) path) =
  (List/join [
    "("
    (Show x (Bits/O path))
    " "
    (Show y (Bits/I path))    
    ")"
  ])

(Show (Term/Var idx) path) = idx
(Show (Term/Open x) path) = "?"

(Show Term/Era path) = "*"

(Show (Term/Sup x y) path) =
  (List/join [
    "{"
    (Show x (Bits/O path))
    " "
    (Show y (Bits/I path))    
    "}"
  ])

(Show (Term/Cln get) path) =
  (Show (get 1) path)

(Print x) = (Show x Bits/E)

(main)=
  let zero = (Term/Lam λf
    let * = (Erase f)
    (Term/Lam λx x)
  )

  let one = (Term/Lam λf
              let (f0, f1) = (DUP f)
              (Term/Lam λx
                (Term/App
                  f0
                  (Term/App
                    f1
                    x
                  )
                )
              )
            )
  
    let succ = 
                (Term/Lam λn
                  (Term/Lam λf
                    let (f0, f1) = (DUP f)
                    (Term/Lam λx
                      (Term/App
                        f0
                        (Term/App
                          (Term/App
                            n
                            f1
                          )
                          x
                        )
                      )
                    )
                  )
                )
    # (Print one)
    # (Normal one)
    (Normal (Term/App succ zero))
    (Normal)