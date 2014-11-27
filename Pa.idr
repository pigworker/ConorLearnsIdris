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


thin : Fin (S n) -> Fin n -> Fin (S n)
thin FZ j = FS j
thin (FS i) FZ = FZ
thin (FS i) (FS j) = FS (thin i j)

data Thick : Fin (S n) -> Fin (S n) -> Type where
  hit  : Thick i i
  miss : (j : Fin n) -> Thick i (thin i j)

total thick : (i, j : Fin (S n)) -> Thick i j
thick FZ FZ = hit
thick FZ (FS j) = miss j
thick {n = Z} (FS FZ) _ impossible
thick {n = S _} (FS i) FZ = miss FZ
thick {n = S _} (FS i) (FS j) with (thick i j)
  thick (FS i) (FS i) | hit = hit
  thick (FS i) (FS (thin i x)) | (miss x) = miss (FS x)

total moreOn : {G : Vect n Type} ->
        (i : Fin n) -> Grammar G (index i G) ->
        index i G -> Grammar G (index i G)
moreOn i (ret y) x = naw
moreOn {n = Z} _ (rec FZ k) x impossible
moreOn {n = S _} i (rec j k) x with (thick i j)
  moreOn i (rec i k) x | hit = k x
  moreOn i (rec (thin i y) k) x | (miss y) = naw
moreOn i (eat f g) x = naw
moreOn i naw x = naw
moreOn i (g <+> h) x = moreOn i g x <+> moreOn i h x

total mayMoreOn : {G : Vect n Type} ->
        (i : Fin n) -> Grammar G (index i G) ->
        index i G -> Grammar G (index i G)
mayMoreOn i g x = moreOn i g x <+> ret x

using (n : Nat, G : Vect n Type, X : Type, Y : Type, Z : Type)
  data PStack : Vect n Type -> Type -> Type -> Type where
    done : PStack G X X
    bind : (X -> Grammar G Y) -> PStack G Y Z -> PStack G X Z
    more : Bool -> (i : Fin n) -> (X = index i G) -> PStack G X Y -> PStack G X Y

  hingmy : PStack G X Y -> PStack G X Y
  hingmy (more True i p (more False j q ks)) = more True i p (more False j q (hingmy ks))
  hingmy (more b i q ks) = more True i q (more False i q (hingmy ks))
  hingmy (bind k ks) = bind k (hingmy ks)
  hingmy done = done

total parsing : {G : Vect n Type} -> {X, Y : Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (rs : List (Fin n)) ->
        (ls : List (Fin n)) ->
        Grammar G X -> PStack G X Y ->
        List Char -> List Y
parsing gs rs ls (ret x) done [] = [x]
parsing gs rs ls (ret x) (bind k ks) s = parsing gs rs ls (k x) ks s
parsing gs rs ls (ret x) (more b i Refl ks) s =
  parsing gs rs ls (if b then mayMoreOn i (gs i) x else ret x) ks s
parsing gs rs (l :: ls) (rec i k) ks s =
  if i == l
    then parsing gs rs ls (gs i) (more False i Refl (bind k ks)) s
    else parsing gs rs ls (rec i k) ks s
parsing gs rs ls (eat p k) ks (c :: s) =
  if p c
  then parsing gs rs rs (k c) (hingmy ks) s
  else []
parsing gs rs ls (g <+> h) ks s =
  parsing gs rs ls g ks s ++ parsing gs rs ls h ks s
parsing _ _ _ _ _ _ = []

total fins : (n : Nat) -> List (Fin n)
fins Z = []
fins (S n) = FZ :: map FS (fins n)

eatIf : {n : Nat} -> {G : Vect n Type} -> (Char -> Bool) -> Grammar G Char
eatIf p = eat p ret

punc : {n : Nat} -> {G : Vect n Type} -> Char -> Grammar G ()
punc c = pure () <$ eatIf (c==)

gimme : {n : Nat} -> {G : Vect n Type} -> (i : Fin n) -> Grammar G (index i G)
gimme i = rec i ret

parse : {n : Nat} -> {G : Vect n Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) ->
        String -> List (index i G)
parse {n=n} gs i s = parsing gs rs rs (gimme i) done (unpack s) where rs = fins n

data Tree = Leaf | Node Tree Tree

myG : Vect 1 Type
myG = [Tree]

mygs : (i : Fin 1) -> Grammar myG (index i myG)
mygs FZ = (pure Leaf <$ punc '*')
      <+> (pure Node <$> gimme FZ <$ punc '^' <$> gimme FZ)
      <+> (pure id <$ punc '(' <$> gimme FZ <$ punc ')')


