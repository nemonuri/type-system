module

public section

theorem Nat.add_assoc_symm (n₁ n₂ n₃: Nat) : n₁ + (n₂ + n₃) = n₁ + n₂ + n₃ := Nat.add_assoc n₁ n₂ n₃ |> Eq.symm

end --public
