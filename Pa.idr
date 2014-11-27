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

GRAMMAR : Vect n Type -> Type
GRAMMAR {n = n} G = (i : Fin n) -> Grammar G (index i G)

eatIf : {n : Nat} -> {G : Vect n Type} -> (Char -> Bool) -> Grammar G Char
eatIf p = eat p ret

punc : {n : Nat} -> {G : Vect n Type} -> Char -> Grammar G ()
punc c = pure () <$ eatIf (c==)

gimme : {n : Nat} -> {G : Vect n Type} -> (i : Fin n) -> Grammar G (index i G)
gimme i = rec i ret

{-
total thin : Fin (S n) -> Fin n -> Fin (S n)
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
-}

total fins : {n : Nat} -> List (Fin n)
fins {n = Z} = []
fins {n = S k} = FZ :: map FS fins

total nulling : {G : Vect n Type} -> {X : Type} ->
        (GRAMMAR G) ->
        List (Fin n) ->
        Grammar G X -> List X
nulling gs ls (ret x) = [x]
nulling gs ls (g <+> h) = nulling gs ls g ++ nulling gs ls h
nulling gs (l :: ls) (rec i k) =
  if i == l then [x | y <- nulling gs ls (gs i), x <- nulling gs ls (k y)]
    else nulling gs ls (rec i k)
nulling _ _ _ = []

total nulls :  {G : Vect n Type} ->
        ((i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) -> List (index i G)
nulls gs i = nulling gs fins (gimme i)

decide : {X, T : Type} -> Dec X -> (X -> T) -> ((X -> Void) -> T) -> T
decide (Yes x) y n = y x
decide (No nx) y n = n nx

tsbus : {X : Type} -> {x, y : X} -> x = y -> (P : X -> Type) -> P y -> P x
tsbus Refl P p = p

total moreOn : {G : Vect n Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) -> Grammar G (index i G) ->
        index i G -> Grammar G (index i G)
moreOn gs i (ret y) x = naw
moreOn {G=G} gs i (rec j k) x = decide (decEq i j) 
  (\ q => tsbus q (\ j => index j G -> Grammar G (index i G)) k x)
  (\ _ => Prelude.Foldable.foldr
    (\ y => \ g => moreOn gs i (k y) x <+> g) naw (nulls gs j))
moreOn gs i (eat f g) x = naw
moreOn gs i naw x = naw
moreOn gs i (g <+> h) x = moreOn gs i g x <+> moreOn gs i h x

total mayMoreOn : {G : Vect n Type} ->
        ((i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) -> Grammar G (index i G) ->
        index i G -> Grammar G (index i G)
mayMoreOn gs i g x = moreOn gs i g x <+> ret x

using (n : Nat, G : Vect n Type, X : Type, Y : Type, Z : Type)
  data PStack : Vect n Type -> Type -> Type -> Type where
    done : PStack G X X
    bind : (X -> Grammar G Y) -> PStack G Y Z -> PStack G X Z
    more : (i : Fin n) -> PStack G (index i G) Y -> PStack G (index i G) Y
    hing : PStack G X Y -> PStack G X Y

  total hingmy : (gs : (i : Fin n) -> Grammar G (index i G)) -> PStack G X Y -> PStack G X Y
  hingmy gs (more i ks) = hing (bind (mayMoreOn gs i (gs i)) (more i (hingmy gs ks)))
  hingmy gs (bind k ks) = bind k (hingmy gs ks)
  hingmy gs done = done
  hingmy gs (hing ks) = hing ks

total parsing : {G : Vect n Type} -> {X, Y : Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (rs : List (Fin n)) ->
        (ls : List (Fin n)) ->
        Grammar G X -> PStack G X Y ->
        List Char -> List Y
parsing gs rs ls (ret x) done [] = [x]
parsing gs rs ls (ret x) (hing ks) s = parsing gs rs ls (ret x) ks s
parsing gs rs ls (ret x) (bind k ks) s = parsing gs rs ls (k x) ks s
parsing gs rs ls (ret x) (more i ks) s = parsing gs rs ls (ret x) ks s
parsing gs rs (l :: ls) (rec i k) ks s =
  if i == l
  then parsing gs rs ls (gs i) (more i (bind k ks)) s
  else parsing gs rs ls (rec i k) ks s
parsing gs rs ls (eat p k) ks (c :: s) =
  if p c
  then parsing gs rs rs (k c) (hing (hingmy gs ks)) s
  else []
parsing gs rs ls (g <+> h) ks s =
  parsing gs rs ls g ks s ++ parsing gs rs ls h ks s
parsing _ _ _ _ _ _ = []

parse : {n : Nat} -> {G : Vect n Type} ->
        (gs : (i : Fin n) -> Grammar G (index i G)) ->
        (i : Fin n) ->
        String -> List (index i G)
parse {n=n} gs i s = parsing gs fins fins (gimme i) done (unpack s)

data Tree = Leaf | Node Tree Tree

myG : Vect 1 Type
myG = [Tree]

mygs : GRAMMAR myG
mygs FZ = (pure Leaf <$ punc '*')
      <+> (pure Node <$> gimme FZ <$ punc '^' <$> gimme FZ)
      <+> (pure id <$ punc '(' <$> gimme FZ <$ punc ')')

myG' : Vect 2 Type
myG' = [Tree, ()]
mygs' : GRAMMAR myG'
mygs' FZ = gimme (FS FZ) $> (((pure Leaf) <$ punc '*')
      <+> (pure Node <$> gimme FZ <$ gimme (FS FZ) <$ punc '^' <$> gimme FZ)
      <+> (pure id <$ punc '(' <$> gimme FZ <$ gimme (FS FZ) <$ punc ')')) {- <$ gimme (FS FZ) -}
mygs' (FS FZ) = (punc ' ' <$ gimme (FS FZ)) <+> (pure ())
