import FormalConjectures.GreensOpenProblems.«31»

-- Reduction Green31.green_31.variants.abelian.R1 of Ben Green's Open Problem 31 — abelian
-- Credit: @loris-olsem
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Green31_green_31_variants_abelian_R1

def H1 : Prop :=
  ∀ L : ℕ, 0 < L → ∃ A : Finset ℕ,
    A ⊆ Finset.range L ∧ IsSidon (A : Set ℕ) ∧ L ≤ 4 * A.card ^ 2

def H2 : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
    80 ^ 6 < Fintype.card G →
    (∀ (r : ℕ) (d : Fin r → ℕ), (∀ i, 2 ≤ d i) →
      Nonempty (G ≃+ ((i : Fin r) → ZMod (d i))) →
      2500 * (∏ i, ((d i + 1) / 2)) < Fintype.card G) →
    (∀ (K : Type) [Field K] [Fintype K] (f : K × K →+ G),
      Function.Injective f → 10000 * (Fintype.card K) ^ 2 < Fintype.card G) →
    ∃ A : Finset G,
      2 * Real.sqrt (Fintype.card G) +
          75 * (Nat.choose A.card 2 : ℝ) ≤
        75 * ((A.card : ℝ) +
          ((A.offDiag.image (fun z ↦ z.1 + z.2)).card : ℝ))

theorem recover_pair {K : Type} [Field K] {a b c d : K}
    (hs : a + b = c + d) (hp : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hz : (a - c) * (a - d) = 0 := by linear_combination a * hs - hp
  rcases mul_eq_zero.mp hz with h | h
  · have he := sub_eq_zero.mp h
    exact Or.inl ⟨he, by linear_combination hs - he⟩
  · have he := sub_eq_zero.mp h
    exact Or.inr ⟨he, by linear_combination hs - he⟩

theorem field_graph {K G : Type} [Field K] [Fintype K] [AddCommGroup G]
    (f : K × K →+ G) (hf : Function.Injective f) :
    ∃ S : Finset G, Green31.IsGroupSidon (S : Set G) ∧ S.card = Fintype.card K := by
  classical
  let g : K → K := fun x ↦ if (2 : K) = 0 then x ^ 3 else x ^ 2
  let t : K → G := fun x ↦ f (x, g x)
  have ht : Function.Injective t := fun a b h ↦ congrArg Prod.fst (hf h)
  refine ⟨Finset.univ.image t, ?_, by rw [Finset.card_image_of_injective _ ht, Finset.card_univ]⟩
  intro a b c d ha hb hc hd h
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hd
  have he : (u, g u) + (v, g v) = (w, g w) + (z, g z) :=
    hf (by simpa only [t, map_add] using h)
  have hs : u + v = w + z := congrArg Prod.fst he
  have hg : g u + g v = g w + g z := congrArg Prod.snd he
  suffices out : (u = w ∧ v = z) ∨ (u = z ∧ v = w) ∨ (u = v ∧ w = z) by
    rcases out with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  by_cases h2 : (2 : K) = 0
  · simp only [g, if_pos h2] at hg
    by_cases hz : u + v = 0
    · have hw := hs.symm.trans hz
      exact Or.inr (Or.inr ⟨by linear_combination u * h2 - hz,
        by linear_combination w * h2 - hw⟩)
    · have h3 : (3 : K) = 1 := by linear_combination h2
      have eqn : 3 * ((u + v) * (u * v - w * z)) = 0 := by
        linear_combination ((u+v)^2 + (u+v)*(w+z) + (w+z)^2 - 3*w*z) * hs - hg
      rw [h3, one_mul] at eqn
      have hp := sub_eq_zero.mp ((mul_eq_zero.mp eqn).resolve_left hz)
      exact (recover_pair hs hp).imp_right Or.inl
  · simp only [g, if_neg h2] at hg
    have eqn : 2 * (u * v - w * z) = 0 := by
      linear_combination (u + v + w + z) * hs - hg
    have hp := sub_eq_zero.mp ((mul_eq_zero.mp eqn).resolve_left h2)
    exact (recover_pair hs hp).imp_right Or.inl

theorem digit_reflection (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 2 ≤ d i) :
    ∃ e : Fin (∏ i, ((d i + 1) / 2)) → ((i : Fin r) → ZMod (d i)),
      ∀ a b c z, e a + e b = e c + e z →
        a.val + b.val = c.val + z.val := by
  induction r with
  | zero =>
    simp only [Fin.prod_univ_zero]
    refine ⟨fun _ i ↦ Fin.elim0 i, ?_⟩
    intro a b c z _
    have := a.isLt
    have := b.isLt
    have := c.isLt
    have := z.isLt
    omega
  | succ r ih =>
    obtain ⟨t, ht⟩ := ih (fun i ↦ d i.succ) (fun i ↦ hd i.succ)
    rw [Fin.prod_univ_succ]
    let B := (d 0 + 1) / 2
    let V := ∏ i : Fin r, ((d i.succ + 1) / 2)
    let de : Fin (B * V) → Fin B × Fin V := finProdFinEquiv.symm
    let e (a : Fin (B * V)) : (i : Fin (r + 1)) → ZMod (d i) :=
      Fin.cons (((de a).1.val : ℕ) : ZMod (d 0)) (t (de a).2)
    refine ⟨e, ?_⟩
    intro a b c z h
    have hhead := congrFun h 0
    change ((de a).1.val : ZMod (d 0)) + (de b).1.val =
      ((de c).1.val : ZMod (d 0)) + (de z).1.val at hhead
    rw [← Nat.cast_add, ← Nat.cast_add] at hhead
    have hb (i j : Fin (B * V)) : (de i).1.val + (de j).1.val < d 0 := by
      have hi := (de i).1.isLt
      have hj := (de j).1.isLt
      dsimp [B] at hi hj
      omega
    have hh := congrArg ZMod.val hhead
    rw [ZMod.val_natCast_of_lt (hb a b), ZMod.val_natCast_of_lt (hb c z)] at hh
    have heq : t (de a).2 + t (de b).2 = t (de c).2 + t (de z).2 :=
      funext fun i ↦ congrFun h i.succ
    have htail := ht _ _ _ _ heq
    have rep (i : Fin (B * V)) : (de i).2.val + V * (de i).1.val = i.val :=
      congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
    rw [← rep a, ← rep b, ← rep c, ← rep z]
    linear_combination htail + V * hh

theorem small_estimate {M : ℝ} (hpos : 0 < M) (hcap : M ≤ 80 ^ 3) :
    M / 100 ≤ M^2 / (80*M) - (M^2)^2 / (2*(80*M)^3) -
      (M^2)^3 / (8*(80*M)^4) := by
  field_simp [ne_of_gt hpos]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hcap) (pow_nonneg hpos.le 6),
    pow_pos hpos 6, mul_nonneg (sub_nonneg.mpr hcap) (pow_nonneg hpos.le 5),
    pow_pos hpos 5, mul_nonneg (sub_nonneg.mpr hcap) (pow_nonneg hpos.le 4),
    pow_pos hpos 4]

lemma size_of_square {n k : ℕ} (h : n ≤ 10000 * k^2) :
    0.01 * Real.sqrt n ≤ (k : ℝ) := by
  have h' : (n : ℝ) ≤ 10000 * (k : ℝ)^2 := by exact_mod_cast h
  have hs : Real.sqrt n ≤ 100 * (k : ℝ) := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  linarith

lemma digit_witness {G : Type} [AddCommGroup G] [Fintype G] (h1 : H1)
    (r : ℕ) (d : Fin r → ℕ) (hd : ∀ i, 2 ≤ d i) (iso : G ≃+ ((i : Fin r) → ZMod (d i)))
    (hc : Fintype.card G ≤ 2500 * (∏ i, (d i + 1) / 2)) :
    ∃ S : Finset G, Green31.IsGroupSidon (S : Set G) ∧ 0.01 * Real.sqrt (Fintype.card G) ≤ S.card := by
  classical
  let L := ∏ i, (d i + 1) / 2
  have hl : 0 < L := Finset.prod_pos fun i _ ↦ by have := hd i; omega
  obtain ⟨A,hA,hSid,hsize⟩ := h1 L hl
  obtain ⟨digits,href⟩ := digit_reflection r d hd
  let idx (x : ↥A) : Fin L := ⟨x.val, Finset.mem_range.mp (hA x.property)⟩
  let f (x : ↥A) := iso.symm (digits (idx x))
  have reflect (a b c z : ↥A) (h : f a + f b = f c + f z) :
      a.val + b.val = c.val + z.val :=
    href _ _ _ _ (by simpa [f] using congrArg iso h)
  have hf : Function.Injective f := by
    intro a b hab
    have hh := reflect a a b a (by rw [hab])
    exact Subtype.ext (Nat.add_right_cancel hh)
  refine ⟨A.attach.image f, ?_, ?_⟩
  · intro a b c z ha hb hc' hz he
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hc'
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hz
    rcases hSid _ a.property _ c.property _ b.property _ z.property (reflect a b c z he) with h | h
    · exact .inl ⟨congrArg f (Subtype.ext h.1),congrArg f (Subtype.ext h.2)⟩
    · exact .inr (.inl ⟨congrArg f (Subtype.ext h.1),congrArg f (Subtype.ext h.2)⟩)
  · rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
    apply size_of_square
    change Fintype.card G ≤ 2500 * L at hc
    omega

lemma mark_delete {α : Type*} (V : Finset α) (E : Finset (Finset α))
    (hne : ∀ e ∈ E, e.Nonempty) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧ V.card ≤ S.card + E.card := by
  classical
  let pick (e : ↥E) := (hne e.val e.property).choose
  let D := E.attach.image pick
  refine ⟨V \ D, Finset.sdiff_subset, ?_, ?_⟩
  · intro e he hs
    let t : ↥E := ⟨e, he⟩
    have hm : pick t ∈ e := (hne e he).choose_spec
    exact (Finset.mem_sdiff.mp (hs hm)).2 (Finset.mem_image_of_mem pick (Finset.mem_attach _ t))
  · have hcard : D.card ≤ E.card := by simpa [D] using (Finset.card_image_le (s := E.attach) (f := pick))
    have h := Finset.le_card_sdiff D V
    omega

lemma powerset_weight {α : Type*} [DecidableEq α] (V e : Finset α) (he : e ⊆ V) (p : ℝ) :
    (∑ T ∈ V.powerset, if e ⊆ T then p ^ T.card * (1-p) ^ (V \ T).card else 0) =
      p ^ e.card := by
  classical
  let q (i : α) : ℝ := if i ∈ e then 0 else 1-p
  calc
    _ = ∑ T ∈ V.powerset, (∏ _i ∈ T, p) * ∏ i ∈ V \ T, q i := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases h : e ⊆ T
      · rw [if_pos h]
        have hq : ∀ i ∈ V \ T, q i = 1-p := by
          intro i hi
          exact if_neg (fun hi' ↦ (Finset.mem_sdiff.mp hi).2 (h hi'))
        rw [Finset.prod_congr rfl hq]
        simp
      · rw [if_neg h]
        obtain ⟨i, hi, hiT⟩ := Finset.not_subset.mp h
        have hz : (∏ j ∈ V \ T, q j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨he hi, hiT⟩) (if_pos hi)
        rw [hz, mul_zero]
    _ = ∏ i ∈ V, (p + q i) := (Finset.prod_add _ _ _).symm
    _ = ∏ i ∈ V, (if i ∈ e then p else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ e <;> simp [q, h]
    _ = _ := by
      rw [Finset.prod_ite]
      have hfilter : V.filter (· ∈ e) = e := by ext i; simp; grind
      simp [hfilter]

lemma finite_alteration {α : Type*} [DecidableEq α] (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, e.Nonempty ∧ e ⊆ V) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧ p * V.card - ∑ e ∈ E, p ^ e.card ≤ S.card := by
  classical
  let w (T : Finset α) := p ^ T.card * (1-p) ^ (V \ T).card
  let hits (T : Finset α) := E.filter (· ⊆ T)
  let score (T : Finset α) : ℝ := T.card - ((hits T).card : ℝ)
  have mass : ∑ T ∈ V.powerset, w T = 1 := by simpa [w] using powerset_weight V ∅ (by simp) p
  have moment (B : Finset (Finset α)) (hB : ∀ e ∈ B, e ⊆ V) :
      (∑ T ∈ V.powerset, w T * ((B.filter (· ⊆ T)).card : ℝ)) = ∑ e ∈ B, p ^ e.card := by
    calc
      _ = ∑ T ∈ V.powerset, ∑ e ∈ B, if e ⊆ T then w T else 0 := by
        apply Finset.sum_congr rfl
        intro T _
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e he ↦ powerset_weight V e (hB e he) p
  have first : (∑ T ∈ V.powerset, w T * T.card) = p * V.card := by
    let B := V.image (fun i ↦ ({i} : Finset α))
    have hB : ∀ e ∈ B, e ⊆ V := by simp [B]
    have hf (T : Finset α) (hT : T ⊆ V) :
        B.filter (· ⊆ T) = T.image (fun i ↦ ({i} : Finset α)) := by
      ext s
      simp [B]
      grind
    calc
      _ = ∑ T ∈ V.powerset, w T * ((B.filter (· ⊆ T)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [hf T (Finset.mem_powerset.mp hT), Finset.card_image_of_injective]
        exact fun _ _ h ↦ Finset.singleton_injective h
      _ = _ := by
        rw [moment B hB, Finset.sum_image]
        · simp [mul_comm]
        · exact Finset.singleton_injective.injOn
  have average : (∑ T ∈ V.powerset, w T * score T) = p * V.card - ∑ e ∈ E, p ^ e.card := by
    simp only [score, hits, mul_sub, Finset.sum_sub_distrib, first, moment E (fun e he ↦ (hE e he).2)]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image V.powerset score ⟨∅, by simp⟩
  have hbound : p * V.card - ∑ e ∈ E, p ^ e.card ≤ score T := by
    rw [← average]
    calc
      _ ≤ ∑ U ∈ V.powerset, w U * score T := by
        apply Finset.sum_le_sum
        intro U hU
        exact mul_le_mul_of_nonneg_left (hmax U hU)
          (mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp') _))
      _ = _ := by rw [← Finset.sum_mul, mass, one_mul]
  obtain ⟨S, hS, hfree, hcard⟩ := mark_delete T (hits T) (fun e he ↦ (hE e (Finset.mem_filter.mp he).1).1)
  refine ⟨S, hS.trans (Finset.mem_powerset.mp hT), ?_, hbound.trans ?_⟩
  · intro e he hes
    exact hfree e (Finset.mem_filter.mpr ⟨he, hes.trans hS⟩) hes
  · dsimp [score]
    exact sub_le_iff_le_add.mpr (by exact_mod_cast hcard)

lemma fiber_bound {α β : Type*} [DecidableEq β] (U : Finset α) (E : Finset β) (f : α → β)
    (k : ℕ) (h : ∀ e ∈ E, k ≤ (U.filter (fun t ↦ f t = e)).card) :
    k * E.card ≤ U.card := by
  calc
    _ = ∑ _e ∈ E, k := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum h
    _ ≤ U.card := by rw [Finset.sum_card_fiberwise_eq_card_filter]; exact Finset.card_filter_le ..

lemma triple_edges {G : Type} [AddCommGroup G] [DecidableEq G] (V : Finset G) :
    ∃ E : Finset (Finset G),
      (∀ e ∈ E, e.card = 3 ∧ e ⊆ V ∧ ∃ x y z : G, x+x = y+z ∧ e = {x,y,z}) ∧
      (∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, y ≠ z → x+x = y+z → {x,y,z} ∈ E) := by
  classical
  let E := (V.powersetCard 3).filter fun e ↦ ∃ x y z : G, x+x = y+z ∧ e = {x,y,z}
  refine ⟨E, ?_, ?_⟩
  · intro e he
    obtain ⟨h, ht⟩ := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_powersetCard.mp h).2, (Finset.mem_powersetCard.mp h).1, ht⟩
  · intro x hx y hy z hz hyz heq
    have hxy : x ≠ y := by rintro rfl; exact hyz (add_left_cancel heq)
    have hxz : x ≠ z := by rintro rfl; exact hyz (add_right_cancel heq).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,hx,hy,hz], by simp [hxy,hxz,hyz]⟩,
      x,y,z,heq,rfl⟩

lemma triple_count {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (E : Finset (Finset G))
    (hE : ∀ e ∈ E, e.card = 3 ∧ ∃ x y z : G, x+x = y+z ∧ e = {x,y,z}) :
    2 * E.card ≤ (Fintype.card G)^2 := by
  classical
  let f (t : G × G) : Finset G := {t.1,t.2,t.1+t.1-t.2}
  have h := fiber_bound Finset.univ E f 2 (by
    intro e he
    obtain ⟨hc,x,y,z,hs,rfl⟩ := hE e he
    have hyz : y ≠ z := by rintro rfl; simp at hc; grind
    let P : Finset (G × G) := {(x,y),(x,z)}
    have hp : P.card = 2 := by simp [P, hyz]
    rw [← hp]
    apply Finset.card_le_card
    have hz : x+x-y=z := by rw [hs]; abel
    have hy : x+x-z=y := by rw [hs]; abel
    intro t ht
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [f,hz,hy,Finset.pair_comm z y])
  simpa [sq] using h

set_option maxHeartbeats 1600000 in
lemma eight_orders {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a b c d : G) (hs : a+b=c+d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    8 ≤ ((Finset.univ : Finset (G × G × G)).filter (fun t ↦
      ({t.1,t.2.1,t.2.2,t.1+t.2.1-t.2.2} : Finset G) = {a,b,c,d})).card := by
  classical
  let P : Finset (G × G × G) :=
    {(a,b,c),(b,a,c),(a,b,d),(b,a,d),(c,d,a),(d,c,a),(c,d,b),(d,c,b)}
  have hp : P.card = 8 := by
    simp [P, Prod.ext_iff, hab, hac, had, hbc, hbd, hcd,
      Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  rw [← hp]
  apply Finset.card_le_card
  intro t ht
  simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
  have h1 : a+b-c=d := by rw [hs]; abel
  have h2 : b+a-c=d := by rw [add_comm b a,h1]
  have h3 : a+b-d=c := by rw [hs]; abel
  have h4 : b+a-d=c := by rw [add_comm b a,h3]
  have h5 : c+d-a=b := by rw [← hs]; abel
  have h6 : d+c-a=b := by rw [add_comm d c,h5]
  have h7 : c+d-b=a := by rw [← hs]; abel
  have h8 : d+c-b=a := by rw [add_comm d c,h7]
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h1,h2,h3,h4,h5,h6,h7,h8] <;>
    ext v <;> simp only [Finset.mem_insert,Finset.mem_singleton,or_assoc,or_left_comm,or_comm]

lemma quadruple_edges {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] :
    ∃ E : Finset (Finset G), (∀ e ∈ E, e.card = 4) ∧
      (∀ a b c d : G, a+b = c+d → a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        {a,b,c,d} ∈ E) ∧ 8 * E.card ≤ (Fintype.card G)^3 := by
  classical
  let E := ((Finset.univ : Finset G).powersetCard 4).filter fun e ↦
    ∃ a b c d : G, a+b=c+d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ e = {a,b,c,d}
  refine ⟨E, fun e he ↦ (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2, ?_, ?_⟩
  · intro a b c d h hab hac had hbc hbd hcd
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,by simp [hab,hac,had,hbc,hbd,hcd]⟩,a,b,c,d,h,hab,hac,had,hbc,hbd,hcd,rfl⟩
  · let f (t : G × G × G) : Finset G := {t.1,t.2.1,t.2.2,t.1+t.2.1-t.2.2}
    have h := fiber_bound Finset.univ E f 8 (by
      intro e he
      obtain ⟨a,b,c,d,hs,hab,hac,had,hbc,hbd,hcd,rfl⟩ := (Finset.mem_filter.mp he).2
      exact eight_orders a b c d hs hab hac had hbc hbd hcd)
    simpa [pow_succ,mul_assoc] using h

lemma pair_mem {G : Type} [DecidableEq G] {A : Finset G} {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) : {a,b} ∈ A.powersetCard 2 :=
  Finset.mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb], by simp [hne]⟩

lemma restricted_pairs {G : Type} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    (A.powersetCard 2).image (fun u ↦ u.sum id) = A.offDiag.image (fun z ↦ z.1 + z.2) := by
  ext s
  constructor
  · intro hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hsub,hc⟩ := Finset.mem_powersetCard.mp hu
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
    refine Finset.mem_image.mpr ⟨(a,b), Finset.mem_offDiag.mpr ⟨hsub (by simp), hsub (by simp), hab⟩, ?_⟩
    simp [hab]
  · intro hs
    obtain ⟨⟨a,b⟩, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_image.mpr ⟨{a,b}, pair_mem ha hb hab, by simp [hab]⟩

lemma unique_restriction {G : Type} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    ∃ W ⊆ A, Set.InjOn (fun u : Finset G ↦ u.sum id) (W.powersetCard 2 : Set (Finset G)) ∧
      A.card + (A.offDiag.image (fun z ↦ z.1 + z.2)).card ≤ W.card + Nat.choose A.card 2 := by
  classical
  let P := A.powersetCard 2
  let f (u : Finset G) := u.sum id
  obtain ⟨R,hR,hinj,himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (P : Set (Finset G)) (P.image f) (by simpa using (Set.surjOn_image (f := f) (s := (P : Set (Finset G)))))
  have hcard := Finset.card_sdiff_add_card_eq_card (show R ⊆ P from hR)
  have hRcard : R.card = (P.image f).card := by rw [← himg, Finset.card_image_of_injOn hinj]
  obtain ⟨W,hW,havoid,hsize⟩ := mark_delete A (P \ R) (by
    intro e he
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp he).1).2
    exact Finset.card_pos.mp (by omega))
  have kept {u : Finset G} (hu : u ∈ W.powersetCard 2) : u ∈ R := by
    obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hu
    by_contra h
    exact havoid u (Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨hs.trans hW,hc⟩, h⟩) hs
  refine ⟨W,hW,fun _ hu _ hv he ↦ hinj (kept hu) (kept hv) he, ?_⟩
  rw [← restricted_pairs, ← Finset.card_powersetCard]
  change A.card + (P.image f).card ≤ W.card + P.card
  omega

lemma triple_count_unique {G : Type} [AddCommGroup G] [DecidableEq G]
    (W : Finset G) (hw : Set.InjOn (fun u : Finset G ↦ u.sum id) (W.powersetCard 2 : Set (Finset G)))
    (E : Finset (Finset G))
    (hE : ∀ e ∈ E, e.card = 3 ∧ e ⊆ W ∧ ∃ x y z : G, x+x = y+z ∧ e = {x,y,z}) :
    E.card ≤ W.card := by
  classical
  have rep (e : ↥E) : ∃ x ∈ W, ∃ u ∈ W.powersetCard 2, u.sum id = x+x ∧ e.val = insert x u := by
    obtain ⟨hc,hs,x,y,z,he,h⟩ := hE e e.property
    rw [h] at hc hs
    have hyz : y ≠ z := by
      rintro rfl
      simp at hc
      have := Finset.card_le_two (a := x) (b := y)
      omega
    exact ⟨x,hs (by simp),{y,z},pair_mem (hs (by simp)) (hs (by simp)) hyz, by simpa [hyz] using he.symm,h⟩
  choose x hx u hu hsum hrep using rep
  let center (e : ↥E) : ↥W := ⟨x e, hx e⟩
  apply Finset.card_le_card_of_injective (f := center)
  intro e t h
  have hxt : x e = x t := congrArg Subtype.val h
  have hut : u e = u t := hw (hu e) (hu t) (by dsimp only; rw [hsum e,hsum t,hxt])
  exact Subtype.ext (by rw [hrep e,hrep t,hxt,hut])

lemma sidon_of_collisions {G : Type} [AddCommGroup G] [DecidableEq G] (S : Finset G)
    (h3 : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, y ≠ z → x+x ≠ y+z)
    (h4 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → c ≠ d → a+b = c+d →
      ({a,b} : Finset G) = {c,d}) : Green31.IsGroupSidon (S : Set G) := by
  intro a b c d ha hb hc hd h
  by_cases hab : a = b
  · subst b
    by_cases hcd : c = d
    · exact .inr (.inr ⟨rfl,hcd⟩)
    · exact (h3 a ha c hc d hd hcd h).elim
  by_cases hcd : c = d
  · subst d
    exact (h3 c hc a ha b hb hab h.symm).elim
  have hp := h4 a ha b hb c hc d hd hab hcd h
  have hmem : a ∈ ({c,d} : Finset G) := hp ▸ Finset.mem_insert_self a _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact .inl ⟨rfl,add_left_cancel h⟩
  · exact .inr (.inl ⟨rfl,add_left_cancel (h.trans (add_comm _ _))⟩)

lemma small_group (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hn : Fintype.card G ≤ 80^6) :
    ∃ S : Finset G, Green31.IsGroupSidon (S : Set G) ∧ 0.01 * Real.sqrt (Fintype.card G) ≤ S.card := by
  classical
  obtain ⟨E3,hE3,mem3⟩ := triple_edges (Finset.univ : Finset G)
  obtain ⟨E4,hE4,mem4,c4⟩ := quadruple_edges (G := G)
  have c3 := triple_count E3 fun e he ↦ ⟨(hE3 e he).1,(hE3 e he).2.2⟩
  let n : ℝ := Fintype.card G
  let M := Real.sqrt n
  let p : ℝ := 1 / (80*M)
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ Fintype.card G from Fintype.card_pos)
  have hm1 : 1 ≤ M := by simpa [M] using Real.sqrt_le_sqrt hn1
  have hm : 0 < M := by linarith
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hp1 : p ≤ 1 := by dsimp only [p]; apply (div_le_one (by positivity)).mpr; linarith
  have hm2 : M^2 = n := Real.sq_sqrt (by linarith)
  have hcap : M ≤ 80^3 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by dsimp only [n]; exact_mod_cast (show Fintype.card G ≤ (80^3)^2 by simpa [← pow_mul] using hn)⟩
  obtain ⟨S,_,hfree,hsize⟩ := finite_alteration (Finset.univ : Finset G) (E3 ∪ E4) (by
    intro e he
    refine ⟨Finset.card_pos.mp ?_,Finset.subset_univ _⟩
    rcases Finset.mem_union.mp he with he | he
    · rw [(hE3 e he).1]; decide
    · rw [hE4 e he]; decide) p hp hp1
  refine ⟨S, sidon_of_collisions S ?_ ?_, ?_⟩
  · intro x hx y hy z hz hyz he
    exact hfree {x,y,z} (Finset.mem_union_left _ (mem3 _ (by simp) _ (by simp) _ (by simp) hyz he))
      (by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,hx,hy,hz])
  · intro a ha b hb c hc d hd hab hcd he
    by_cases hac : a = c
    · subst c; rw [add_left_cancel he]
    by_cases had : a = d
    · subst d; rw [add_left_cancel (he.trans (add_comm _ _)), Finset.pair_comm]
    have hbc : b ≠ c := by
      rintro rfl
      exact had (add_right_cancel (he.trans (add_comm _ _)))
    have hbd : b ≠ d := by rintro rfl; exact hac (add_right_cancel he)
    exact (hfree {a,b,c,d} (Finset.mem_union_right _ (mem4 a b c d he hab hac had hbc hbd hcd)) (by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc,hd])).elim
  · have hdis : Disjoint E3 E4 := Finset.disjoint_left.mpr fun e he hf ↦ by
      have := (hE3 e he).1; have := hE4 e hf; omega
    rw [Finset.sum_union hdis] at hsize
    have t3 : (∑ e ∈ E3, p ^ e.card) = E3.card * p^3 := by
      rw [Finset.sum_congr rfl (fun e he ↦ congrArg (p ^ ·) (hE3 e he).1)]
      simp
    have t4 : (∑ e ∈ E4, p ^ e.card) = E4.card * p^4 := by
      rw [Finset.sum_congr rfl (fun e he ↦ congrArg (p ^ ·) (hE4 e he))]
      simp
    rw [t3,t4,Finset.card_univ] at hsize
    have hc3 : 2 * (E3.card : ℝ) ≤ n^2 := by dsimp only [n]; exact_mod_cast c3
    have hc4 : 8 * (E4.card : ℝ) ≤ n^3 := by dsimp only [n]; exact_mod_cast c4
    have hnum := small_estimate hm hcap
    rw [hm2] at hnum
    have hnum' : M/100 ≤ p*n - n^2/2*p^3 - n^3/8*p^4 := by
      convert hnum using 1 <;> dsimp [p] <;> ring
    change p*n - _ ≤ _ at hsize
    change 0.01 * M ≤ _
    linarith [mul_le_mul_of_nonneg_right hc3 (pow_nonneg hp 3),
      mul_le_mul_of_nonneg_right hc4 (pow_nonneg hp 4)]

lemma large_score {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (A : Finset G)
    (h : 2 * Real.sqrt (Fintype.card G) + 75 * (Nat.choose A.card 2 : ℝ) ≤
      75 * ((A.card : ℝ) + ((A.offDiag.image (fun z ↦ z.1 + z.2)).card : ℝ))) :
    ∃ S : Finset G, Green31.IsGroupSidon (S : Set G) ∧ 0.01 * Real.sqrt (Fintype.card G) ≤ S.card := by
  classical
  obtain ⟨W,_,hw,hsize⟩ := unique_restriction A
  have hsize' : (A.card : ℝ) + ((A.offDiag.image (fun z ↦ z.1 + z.2)).card : ℝ) ≤
      W.card + (Nat.choose A.card 2 : ℝ) := by exact_mod_cast hsize
  have hW : (2/75 : ℝ) * Real.sqrt (Fintype.card G) ≤ W.card := by linarith
  obtain ⟨E,hE,hmem⟩ := triple_edges W
  have hc : (E.card : ℝ) ≤ W.card := by exact_mod_cast triple_count_unique W hw E hE
  obtain ⟨S,hS,hfree,hcard⟩ := finite_alteration W E (fun e he ↦
    ⟨Finset.card_pos.mp (by rw [(hE e he).1]; decide),(hE e he).2.1⟩) (1/2) (by norm_num) (by norm_num)
  refine ⟨S, sidon_of_collisions S ?_ ?_, ?_⟩
  · intro x hx y hy z hz hyz he
    exact hfree _ (hmem _ (hS hx) _ (hS hy) _ (hS hz) hyz he) (by simp [Finset.insert_subset_iff,Finset.singleton_subset_iff,hx,hy,hz])
  · intro a ha b hb c hc' d hd hab hcd he
    apply hw (pair_mem (hS ha) (hS hb) hab) (pair_mem (hS hc') (hS hd) hcd)
    simpa [hab,hcd] using he
  · have ht : (∑ e ∈ E, (1/2 : ℝ) ^ e.card) = E.card * (1/2 : ℝ)^3 := by
      rw [Finset.sum_congr rfl (fun e he ↦ congrArg ((1/2 : ℝ) ^ ·) (hE e he).1)]
      simp
    rw [ht] at hcard
    linarith

theorem main : H1 → H2 → type_of% @Green31.green_31.variants.abelian := by
  classical
  intro h1 h2 G _ _
  by_cases hn : Fintype.card G ≤ 80^6
  · exact small_group G hn
  apply Classical.byContradiction
  intro hnone
  apply hnone
  apply Exists.elim (h2 G (lt_of_not_ge hn) ?_ ?_) large_score
  · intro r d hd hi
    by_contra! h
    exact hnone (digit_witness h1 r d hd hi.some h)
  · intro K _ _ f hf
    by_contra! h
    obtain ⟨S,hs,hc⟩ := field_graph f hf
    exact hnone ⟨S,hs,hc ▸ size_of_square h⟩

end OMA.R_Green31_green_31_variants_abelian_R1
