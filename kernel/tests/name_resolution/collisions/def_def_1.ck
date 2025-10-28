def A : Prop := (P : Prop) -> P

-- A redeclaration of a `def` is an error even if it's identical
def A : Prop := (P : Prop) -> P
