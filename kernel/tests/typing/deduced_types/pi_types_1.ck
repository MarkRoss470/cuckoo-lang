data SomeTy : Type where

data SomeProp : Prop where

def T1 : Type := SomeTy -> SomeTy
def T2 : Prop := SomeTy -> SomeProp
def T3 : Type := SomeProp -> SomeTy
def T4 : Prop := SomeProp -> SomeProp