module Tm

data PROP : Type where
  Tt : Bool -> PROP
  And : PROP -> PROP -> PROP
  All : (A : Type) -> (A -> PROP) -> PROP
  
total Prf : PROP -> Type
Prf (Tt b)    = So b
Prf (And P Q) = (Prf P, Prf Q)
Prf (All A B) = (a : A) -> Prf (B a)

data Dir : Type where
  chk : Dir
  syn : Dir

infixl 2 $

data Tm : Dir -> Type where
  var : Nat -> Tm syn
  ($) : Tm syn -> Tm chk -> Tm syn
  lam : Tm chk -> Tm chk
  clo : Vect l (Tm chk) -> Tm chk -> Tm chk
  neu : Tm syn -> Tm chk

total vall : (a -> PROP) -> Vect n a -> PROP
vall p [] = Tt True
vall p (x :: xs) = And (p x) (vall p xs)

total ok : Nat -> Tm d -> PROP
ok n (var i) = Tt (lt i n)
ok n (f $ a) = And (ok n f) (ok n a)
ok n (lam b) = ok (S n) b
ok n (clo {l=l} g b) = And (assert_total (vall (ok 0) g)) (ok (S l) b)
ok n (neu e) = ok n e

infixl 2 $$

total GTm : Dir -> Nat -> Type
GTm d n = Subset (Tm d) (\ t => Prf (ok n t))

total GEnv : Nat -> Type
GEnv n = Subset (Vect n (Tm chk)) (\ g => Prf (vall (ok 0) g))

total fetch : (i : Nat) -> So (lt i n) -> GEnv n -> GTm chk 0
fetch Z _ (Element (v :: _) (vo, _)) = Element v vo
fetch (S i) io  (Element (_ :: g) (_ , go)) = fetch i io (Element g go)

mutual

  eval : (e : GTm d n) -> (g : GEnv n) -> GTm chk 0
  eval (Element (f $ a) (fo, ao)) g
    = (eval (Element f fo) g) $$ (eval (Element a ao) g)
  eval (Element (lam b) bo) (Element g g0) = Element (clo g b) (g0, bo)
  eval (Element (clo g b) (g0, bo)) _ = Element (clo g b) (g0, bo)
  eval (Element (var i) io) g = fetch i io g
  eval (Element (neu e) eo) g = eval (Element e eo) g

  ($$) : GTm chk 0 -> GTm chk 0 -> GTm chk 0
  (Element (neu e) e0) $$ (Element a a0) = Element (neu (e $ a)) (e0, a0)
  (Element (lam b) b0) $$ (Element a a0)
    = eval (Element b b0) (Element (a :: []) (a0, Oh))
  (Element (clo g b) (g0, bo)) $$ (Element a a0)
    = eval (Element b bo) (Element (a :: g) (a0, g0))
