data Bool : Type where
  | true : Bool
  | false : Bool

def Bool.or (a : Bool) (b : Bool) : Bool := Bool.rec.{1}
    (fun (_ : Bool) => Bool)
    Bool.true
    b
    a

data SomeProp : Bool -> Prop where
  | c : (a : Bool) -> (b : Bool) -> SomeProp (Bool.or a b)

-- Both `a` and `b` are mentioned in the index of `SomeProp.c`, but `SomeProp` is still not large eliminating
-- because they are not used verbatim as an index
def some_prop_rec : Prop := SomeProp.rec.{1}