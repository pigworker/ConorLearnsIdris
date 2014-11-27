module Pa

using (n : Nat, G : (i : Nat) -> LT i n -> Type, X : Type)
  data Grammar : {n : Nat} -> (G : (i : Nat) -> LT i n -> Type) -> Type -> Type where
    ret : X -> Grammar G X
    rec : (i : Nat) -> (l : LT i n) -> (G i l -> Grammar G x) -> Grammar G x
    eat : (Char -> Bool) -> (Char -> Grammar G X) -> Grammar G X
    naw : Grammar G X
    (<&>) : Grammar G X -> Grammar G X -> Grammar G X
    (<+>) : Grammar G X -> Grammar G X -> Grammar G X

nulls : {n : Nat} -> {G : (i : Nat) -> LT i n -> Type} ->
        (gs : (i : Nat) -> (l : LT i n) -> Grammar G (G i l)) ->
        (j : Nat) -> LT j n -> Grammar G X -> List X
nulls gs j l g = ?x
