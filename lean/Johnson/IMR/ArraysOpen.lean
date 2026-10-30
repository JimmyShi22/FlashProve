-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ArraysOpen.lean: THE OPEN LINK's LIST OF ARRAYS IS THE BUILT LINK's,
AND ITS CARRIED ROWS' LAYOUT IS THE PUBLIC ONE: at the proof file's seat, in the goals' scope, from
the fold's return alone. "The state": the verifier's state, the value that the fold of the IOP as
written in Lean carries from sub-protocol to sub-protocol. "The cut k": the state behind the flat
list's first k entries.
  ctx_open: where a link is open, ctxOf's second part bears its rows, number and list of arrays,
    under a mark other than 1 (Johnson/Goal/Meaning/OwnOpen.lean's ctx_of_link, with the mark said).
  blank_first: the blank letters' "first" is the public part's (by the road of
    Johnson/IMR/OwnSeat.lean's
    blank_built).
  built_arr: the blank letters' link number l bears the list of arrays arrOf Z l.
  own_at_cut: the invariant OwnInv (arrOf Z) Z.first.layout at every cut from 2 on, in front of the
    sub-protocols behind the last link.
  arrays_open: THE TOP: at every cut of a link l < 24 at which a link is open (14 l + 3 to
    14 l + 14), and at the head's link from behind "H:2" to behind its last hearing sub-protocol
    (340 to 346): a link L is open, L.link = l, L.arrayOf = Xl.arrayOf for the blank letters' link
    Xl number l, and L.check.rows.layout = Bs.G₀.first.layout = Z.first.layout.
    The cuts in front of the smallness test's draw (14 l + 6; 343) are among these.
NOT HERE: the head's link's cuts 347 to 352 (the walk that is called asks a bound on the cut, which
is at hand only up to a link's last hearing sub-protocol or the next link's first).
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K8's files.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.GroupHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- Where a link is open: what ctxOf bears, and its mark is not 1. -/
theorem ctx_open {t : S} {L : LinkCtx} (h : t.link? = some L) :
    ∃ m, m ≠ 1 ∧ (ctxOf t).2 = some (m, L.check.rows, L.link, L.arrayOf) := by
  unfold S.link? at h
  unfold ctxOf
  cases hh : t.here with
  | between => simp [hh] at h
  | fin a => simp [hh] at h
  | mem a => simp [hh] at h
  | lay a =>
    simp only [hh, Option.some.injEq] at h
    subst h
    exact ⟨0, by decide, rfl⟩
  | att a =>
    simp only [hh, Option.some.injEq] at h
    subst h
    exact ⟨0, by decide, rfl⟩
  | head a =>
    simp only [hh] at h
    by_cases ho : a.opened = true
    · simp only [ho, if_true, Option.some.injEq] at h
      subst h
      exact ⟨2, by decide, by simp [ho]⟩
    · simp [ho] at h

/-- The blank letters' "first" is the public part's. -/
theorem blank_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) : G.first = Z.first := by
  have h' : (ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption =
      some G := h
  cases hx : ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    obtain rfl : G' = G := Option.some.inj h'
    unfold ProofFile.lettersBy at hx
    simp only [bind, Except.bind, pure, Except.pure] at hx
    repeat' split at hx
    all_goals first | contradiction | (cases hx; rfl)

/-- The blank letters' link number l bears the built link's list of arrays. -/
theorem built_arr {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : Stages.LinkH} (hX : G.built[l]? = some Xl) :
    Xl.arrayOf = arrOf Z l := by
  obtain ⟨links, e⟩ := blank_built h
  rw [e] at hX
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hX
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact arrOk_at Z l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The invariant behind the lookups' tie, at every cut from 2 on in front. -/
theorem own_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    OwnInv (arrOf Z) Z.first.layout r.1 := by
  obtain ⟨t, R', C'⟩ := r
  obtain ⟨t₂, R₂, C₂, g⟩ := fold_cut (k := 2) (k - 2)
    (by rw [show 2 + (k - 2) = k by omega]; exact f)
  exact open_fold (seatKeeps_own (A := arrOf Z) (lay := Z.first.layout)) O (arrOk_at Z)
    (fun l Q hQ => letters_arr (IM.base_made O.made).2.2.1 hQ) hk f
    (own_startS O.pub (start_real hS hR O g))

/-- **THE OPEN LINK's LIST OF ARRAYS IS THE BUILT LINK's; ITS CARRIED ROWS' LAYOUT IS THE PUBLIC
ONE.** -/
theorem arrays_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Xl : Stages.LinkH} (hX : Bs.G₀.built[l]? = some Xl)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    {k : Nat} (h1 : 14 * l + 3 + (if l = 24 then 1 else 0) ≤ k)
    (h2 : k ≤ 14 * l + (if l = 24 then 10 else 14))
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    ∃ L, t.link? = some L ∧ L.link = l ∧ L.arrayOf = Xl.arrayOf ∧
      L.check.rows.layout = Bs.G₀.first.layout ∧ Bs.G₀.first.layout = Z.first.layout := by
  have hb := (IM.base_made O.made).2.2.1
  have hk : k ≤ (frontOf c).length := by
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    by_cases e : l = 24
    · subst e
      obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 24 (by omega)
      rw [if_pos rfl] at hlen h2
      obtain ⟨b, eb⟩ : ∃ b, Lk.hear[8]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega : 8 < Lk.hear.length)⟩
      have q := flatIx_le (chainBy_noFront O.chain) eL eb
      rw [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 8] at q
      omega
    · obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr (l + 1) (by omega)
      rw [if_neg e] at h2
      obtain ⟨b, eb⟩ : ∃ b, Lk.hear[0]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by
          have : 7 ≤ Lk.hear.length := by rw [hlen]; split <;> omega
          omega)⟩
      have q := flatIx_le (chainBy_noFront O.chain) eL eb
      rw [IM.flatIx_scope hS hR O (by omega : l + 1 ≤ 24) 0] at q
      omega
  obtain ⟨L, hL, eN, -⟩ := group_all hS hR O hl h1
    (by
      by_cases e : l = 24
      · rw [if_pos e] at h2 ⊢
        omega
      · rw [if_neg e] at h2 ⊢
        omega) f
  have I := own_at_cut hS hR O (by omega) hk f
  obtain ⟨m, hm, hc⟩ := ctx_open hL
  obtain ⟨i1, i2⟩ := I.2 _ hc
  refine ⟨L, hL, eN, ?_, ?_, by rw [blank_first hb]⟩
  · rw [built_arr hb hX, ← eN]
    exact i2 hm
  · rw [blank_first hb]
    exact i1

end

#print axioms ctx_open
#print axioms blank_first
#print axioms built_arr
#print axioms own_at_cut
#print axioms arrays_open

end Meaning.K2
