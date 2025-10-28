data SomeTy.{u} : Type u where

data SomeProp : Prop where

def T1.{u, v} : Type (max u v) := SomeTy.{u} -> SomeTy.{v}
def T2.{u} : Prop := SomeTy.{u} -> SomeProp
def T3.{u} : Type u := SomeProp -> SomeTy.{u}
def T4 : Prop := SomeProp -> SomeProp