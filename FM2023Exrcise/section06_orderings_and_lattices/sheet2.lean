import Mathlib.Tactic

variable (L : Type) [Lattice L] (a b c : L)

example : a ⊔ b = b ⊔ a :=
  by
  apply le_antisymm
  repeat
    . apply sup_le
      . apply le_sup_right
      . apply le_sup_left
  done

example : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  by
  apply le_antisymm
  . apply sup_le
    . apply sup_le
      . apply le_sup_left
      . have h : b ≤ b ⊔ c :=
          by
          apply le_sup_left
        apply le_trans h
        apply le_sup_right
    . have h : c ≤ b ⊔ c :=
        by
        apply le_sup_right
      apply le_trans h
      apply le_sup_right
  . apply sup_le
    . have h : a ≤ a ⊔ b :=
        by
        apply le_sup_left
      apply le_trans h
      apply le_sup_left
    . apply sup_le
      . have h : b ≤ a ⊔ b :=
          by
          apply le_sup_right
        apply le_trans h
        apply le_sup_left
      . apply le_sup_right
  done

lemma inf_le_inf_left' (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  by
  apply le_inf
  . apply inf_le_left
  . have h' : a ⊓ b ≤ b :=
      by
      apply inf_le_right
    apply le_trans h' h
  done


example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) :=
  by
  apply sup_le
  . apply inf_le_inf_left'
    apply le_sup_left
  . apply inf_le_inf_left'
    apply le_sup_right
  done

example : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
  by
  apply le_inf
  . apply sup_le_sup_left
    apply inf_le_left
  . apply sup_le_sup_left
    apply inf_le_right
  done
