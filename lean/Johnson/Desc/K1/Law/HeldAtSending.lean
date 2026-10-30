-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of ours, not in this repository: as copied, it parted from it in three import lines alone.
/-
Johnson/Desc/K1/Law/HeldAtSending.lean: K01_law: THE PROMISE's CLAUSE «held» (at the composed meaning: fun j t a => smpHeld a.2.st a.2.book j t) AROUND A SENDING OF KIND K1, FROM THREE LEMMAS, EACH TAKEN HERE AS
A PREMISE BY ITS Prop's NAME.
  smpHeld_at_commit   (L1 SmpHeldStays ⟹) over a yes of commitAtS the sample of a tenant that the record held in front is held behind [FillL.held at the fifty]
  smpHeld_of_sealed   (S1a OracleNoNew · S1b SeedReadsBack ⟹) a message of the place that is sealed behind the sending (K1.Sealed: the law's own word) is held at its seat [hseal's first half; general in P : Par]
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.SmpHeldStays
import Johnson.Desc.K1.Law.OracleNoNew
import Johnson.Desc.K1.Law.SeedReadsBack
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.First (S)

/-- **«held» rides over a later moment's sending.** -/
theorem smpHeld_at_commit (h : SmpHeldStays) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hy : (commitAtS P link moment arrays : Block S Unit).decide s [r₁, r₂] gs = .ok s') (j t : Nat)
    (h0 : smpHeld s.st s.book j t = true) : smpHeld s'.st s'.book j t = true :=
  (h s.st s'.st s.book s'.book _ j t
    (Rel.commitAtS_keeps groundKeeps_smpStay P link moment arrays s _ gs s' hy)
    (commitAtS_booked P link moment arrays s s' r₁ r₂ gs hy).place h0).2.2.2

/-- **A sealed message of the place is held at its seat.** -/
theorem smpHeld_of_sealed (h1 : OracleNoNew) (h2 : SeedReadsBack) (P : Par) (bk bk' : TreeBook)
    (n : Nat) (St : Statement) (hB : Booked P bk n bk' St.oracles.size) (hn : bk.place.size = n)
    (hold : ∀ (o : Nat) (x : Nat × Nat), bk.place[o]? = some x → x.1 < bk.trees.size)
    (hpart : ∀ i i' : Nat, i < P.sent.size → i' < i →
      ((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
        ((layOf P).tree.getD i 0, (layOf P).part.getD i 0))
    (k : Fin (shapesOf P).length) (e : Nat) (f : (portOmZ P.codes (shapeAt P k) e).Str)
    (hS : Sealed P.codes (shapeAt P k) e f St (St.oracles.size - (shapesOf P).length + k.val))
    (ha : (shapeAt P k).answers = 1) (hp : (OnBytes.Send.pad P.codes (shapeAt P k)).isSome = true)
    (hr : 0 < (shapeAt P k).mainRows ∨ 0 < (shapeAt P k).maskRows) :
    smpHeld St bk' (bk.trees.size + (layOf P).tree.getD k.val 0) ((layOf P).part.getD k.val 0) =
      true := by
  have hl : (shapesOf P).length = P.sent.size := by simp [shapesOf]
  have hk : k.val < P.sent.size := hl ▸ k.isLt
  have ho := h1 P bk bk' n _ hB hn hold hpart k.val hk
  have hix : St.oracles.size - (shapesOf P).length + k.val = n + k.val := by
    have := hB.msgs
    omega
  rw [hix] at hS
  obtain ⟨ρ, y, ⟨hc, x, z, β, t, hx, e1, e2, e3, -, -⟩, -⟩ := hS
  have hrows : smpRows St bk' (bk.trees.size + (layOf P).tree.getD k.val 0)
      ((layOf P).part.getD k.val 0) = some x.sampleRows := by
    unfold smpRows
    rw [ho, Option.bind_some, hx, Option.bind_some, e2, e1, ha, e3]
    rfl
  unfold smpHeld smpSeed
  rw [ho, Option.bind_some, hx, Option.bind_some, hrows, Option.bind_some, e3]
  show ((seedOf St.codes x.shape _).map _).isSome = true
  rw [Option.isSome_map, hc, e1]
  exact h2 P.codes (shapeAt P k) _ z β t (by omega) hp hr

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.smpHeld_at_commit
#print axioms VerifiableInference.Desc.K1.smpHeld_of_sealed
