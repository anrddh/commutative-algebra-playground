import algebra.associated
import algebra.group_power
import ring_theory.ideal_operations
import ring_theory.ideals

universe u

variables {α : Type*}

open_locale classical

/- An element a of a ring α is a zero divisor if there exists a b ∈ α
   such that b ≠ 0 and ab = 0. -/
def is_zero_divisor [comm_ring α] (a : α) := ∃ b : α, b ≠ 0 ∧ a * b = 0

/- An element a of a ring α is nilpotent if there exists a n ∈ ℕ such
   that a^n = 0. -/
def is_nilpotent [comm_ring α] (a : α) := ∃ n : ℕ, a ^ n = 0

/- 0 is nilpotent. -/
theorem zero_is_nilpotent [comm_ring α] : is_nilpotent (0 : α) :=
  exists.intro 1 (by simp)

theorem exists_min_pow_zero_of_nilpotent [comm_ring α] :
  ∀ a : α, is_nilpotent a → ∃ m : ℕ, a^m = 0 ∧ ∀ n : ℕ, n < m → a^n ≠ 0
:=
begin
  rintros a hna,
  use nat.find hna,
  split,
  { exact nat.find_spec hna},
  { intro n,
    exact nat.find_min hna}
end

theorem eq_mul [comm_ring α] (a : α) (ha : (1 : α) = 0) : a = 0
:=
begin
  have h : (a * 1 = a * 0) := eq.subst ha rfl,
  simp at h,
  exact h
end

/- All nonzero nilpotents are zerodivisors. -/
theorem nz_nilpotent_is_zerodivisor [comm_ring α] :
  ∀ a : α, is_nilpotent a → a ≠ 0 → is_zero_divisor a
:=
begin
  intros a ha ha',
  unfold is_zero_divisor,
  unfold is_nilpotent at ha,
  have h := exists_min_pow_zero_of_nilpotent a ha,
  cases h with m hm,
  cases m with,
  { rw pow_zero at hm,
    have haz := eq_mul a hm.left,
    contradiction },
  { cases m with,
    { simp at hm,
      have haz := hm.left,
      contradiction },
    { let n := m + 1,
      use a ^ n,
      rw nat.succ_eq_add_one at hm,
      rw nat.succ_eq_add_one at hm,
      simp at hm,
      split,
      { have hn : n < m + 2,
        simp,
        exact hm.right n hn },
      { rw <- pow_succ,
        exact hm.left, },
    }
  }
end

/- Zero is a zero divisor in a nonzero ring. -/
theorem zero_zero_divisor_in_nz_ring [nonzero_comm_ring α]
  : is_zero_divisor (0 : α) :=
exists.intro 1 ⟨one_ne_zero, by simp⟩

/- All nilpotents are zero divisors in a nonzero ring. -/
theorem nonzero_ring_nilpotent_is_zerodivisor [nonzero_comm_ring α]
  : ∀ a : α, is_nilpotent a → is_zero_divisor a
:= assume a : α,
   assume ha : is_nilpotent a,
   classical.by_cases (assume hz  : a = 0, by simp[hz, zero_zero_divisor_in_nz_ring])
                      (assume hnz : a ≠ 0, nz_nilpotent_is_zerodivisor a ha hnz)

open ideal

/- The nilradical of a ring α is the radical of (0). -/
def nilradical [comm_ring α] := radical (span ({ 0 } : set α))

/- The elements of the nilradical are precisely the nilpotents of α -/
theorem elem_nilradical_nilpotent [comm_ring α] :
  ∀ a : α, a ∈ (@nilradical α).carrier ↔ is_nilpotent a
:= sorry

/- A ring is reduced if its nilradical is the trivial ideal (0) -/
class reduced_ring (α : Type u) extends comm_ring α :=
  (is_reduced : nilradical = span ({ 0 } : set α))

/- The zero ideal is prime in an integral domain. -/
theorem zero_is_prime_in_id [integral_domain α] : (span ({0} : set α)).is_prime
  :=
begin
-- Our strategy is to show that the kernel of the identity α → α is
-- (0) and then apply the ker_is_prime theorem.
let id_hom := @id α,
have ker_of_id_is_prime := ring_hom.ker_is_prime id_hom,
end

/- All integral domains are reduced. -/
theorem integral_domains_are_reduced [integral_domain α] : reduced_ring α
  := is_reduced = is_prime.radical zero_is_prime_in_id
