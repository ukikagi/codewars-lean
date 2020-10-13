universes u

inductive mytree (A : Type u) : Type u
| leaf : A → mytree
| branch : A → mytree → mytree → mytree

def flip_mytree {A : Type u} : mytree A → mytree A
| t@(mytree.leaf _)     := t
| (mytree.branch a l r) := mytree.branch a (flip_mytree r) (flip_mytree l)
