module Pa

using (n : Nat, G : Vect n Type, X : Type)
  data Grammar : {n : Nat} -> (G : Vect n Type) -> Type -> Type where
    ret : X -> Grammar G X
    rec : (i : Fin n) -> (index i G -> Grammar G x) -> Grammar G x
    eat : (Char -> Bool) -> (Char -> Grammar G X) -> Grammar G X
    naw : Grammar G X
    (<+>) : Grammar G X -> Grammar G X -> Grammar G X

  instance Functor (Grammar G) where
    map f (ret x) = ret (f x)
    map f (rec i k) = rec i (\ y => map f (k y))
    map f (eat g k) = eat g (\ c => map f (k c))
    map f naw = naw
    map f (g <+> h) = map f g <+> map f h
    
  instance Applicative (Grammar G) where
    pure = ret
    (ret f) <$> gs = map f gs
    (rec i k) <$> gs = rec i (\ y => k y <$> gs)
    (eat g k) <$> gs = eat g (\ c => k c <$> gs)
    naw <$> gs = naw
    (g <+> h) <$> gs = (g <$> gs) <+> (h <$> gs)

  instance Monad (Grammar G) where
    (ret x) >>= l = l x
    (rec i k) >>= l = rec i (\ y => k y >>= l)
    (eat g k) >>= l = eat g (\ c => k c >>= l)
    naw >>= l = naw
    (g <+> h) >>= l = (g >>= l) <+> (h >>= l)
 
total parsing : {G : Vect n Type} -> {X : Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (rs : List (Fin n)) ->
        (ls : List (Fin n)) ->
        Grammar G X ->
        List Char -> List X
parsing gs rs ls (ret x) [] = [x]
parsing gs rs ls (ret x) (_ :: _) = []
parsing gs rs [] (rec i k) s = []
parsing gs rs (l :: ls) (rec i k) s =
  if i == l
  then parsing gs rs ls (gs i >>= k) s
  else parsing gs rs ls (rec i k) s
parsing gs rs ls (eat p k) [] = []
parsing gs rs ls (eat p k) (c :: s) =
  if p c
  then parsing gs rs rs (k c) s
  else []
parsing gs rs ls naw s = []
parsing gs rs ls (g <+> h) s =
  parsing gs rs ls g s ++ parsing gs rs ls h s

total fins : (n : Nat) -> List (Fin n)
fins Z = []
fins (S n) = FZ :: map FS (fins n)

total parse : {n : Nat} -> {G : Vect n Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) ->
        String -> List (index i G)
parse {n=n} gs i s = parsing gs rs rs (gs i) (unpack s) where rs = fins n ++ fins n

eatIf : {n : Nat} -> {G : Vect n Type} -> (Char -> Bool) -> Grammar G Char
eatIf p = eat p ret

punc : {n : Nat} -> {G : Vect n Type} -> Char -> Grammar G ()
punc c = pure () <$ eatIf (c==)

gimme : {n : Nat} -> {G : Vect n Type} -> (i : Fin n) -> Grammar G (index i G)
gimme i = rec i ret

data Tree = Leaf | Node Tree Tree

myG : Vect 1 Type
myG = [Tree]

mygs : (i : Fin 1) -> Grammar myG (index i myG)
mygs FZ = (pure Leaf <$ punc '*')
      <+> (pure Node <$> gimme FZ <$ punc '^' <$> gimme FZ)
      <+> (pure id <$ punc '(' <$> gimme FZ <$ punc ')')


