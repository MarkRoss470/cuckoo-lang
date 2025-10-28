data SomeTy : Type where

data SomeProp : Prop where

data SomeDepTy.{u} : (T : Sort u) -> T -> Type u where

def T1 : Type 1 := (x : SomeTy) -> SomeDepTy.{1} SomeTy x
def T2 : Type := (x : SomeProp) -> SomeDepTy.{0} SomeProp x
def T3.{u} : Type u := (T : Sort u) -> (x : T) -> SomeDepTy.{u} T x
