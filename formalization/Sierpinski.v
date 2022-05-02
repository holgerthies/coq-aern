Require Import Kleene.

Section S_Defs.
  Generalizable Variable K.
  Context `(klb : LazyBool K).
  Definition sierp :=  {k : K | k <> lazy_bool_false}.
  
End S_Defs.
