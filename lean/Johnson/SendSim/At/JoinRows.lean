-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/JoinRows.lean: the implications that carry the general model's two statements to
the level of rows. Spec.sendExact and Spec.readUnif imply Spec.rowsExact; Spec.sendFresh,
Spec.readUnif and Spec.spentUnif imply Spec.rowsFresh. It claims no property of the protocol: not
hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for the instance
(sender P ride, names, readC, wOf), Johnson/SendSim/At/Bridge.lean, "Terms of the instance". Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves.
  rowsExact_of_core   Spec.sendExact and Spec.readUnif imply Spec.rowsExact.
  rowsFresh_of_core   Spec.sendFresh, Spec.readUnif and Spec.spentUnif imply Spec.rowsFresh.
  fresh_leg           The step that rowsFresh_of_core shares with rowsFreshAny_of_core. Its premises
                      are Spec.sendFresh, Spec.readUnif, the four premises of Spec.rowsExact,
                      MendsOff at the instance for the sets of spent and known names, and a function
                      that satisfies SpentBack and maps uniform values to uniform runs. It concludes
                      the equation of Spec.rowsFresh.
  map3                The image of a distribution under a composite of three functions.

Limits.
Implications only: this file proves none of the named propositions at either end, so it proves no
equation between distributions by itself. The premises are proved as sendExact and sendFresh in
Johnson/SendSim/CoreProofs.lean, as readUnif in Johnson/SendSim/At/ReadUnif.lean and as spentUnif in
Johnson/SendSim/At/SpentUnif.lean.
fresh_leg concludes an equation between distributions, but the condition on the spender
(SpenderClear) is not among its premises. It is a tool for the two proofs that call it and not a
result of its own.

How it fits. Spec.sendExact and Spec.sendFresh are stated in Johnson/SendSim/Defs.lean,
Spec.readUnif in Johnson/SendSim/At/Bridge.lean, Spec.rowsExact in Johnson/SendSim/At/Sim.lean,
Spec.spentUnif, SpentBack and Spec.rowsFresh in Johnson/SendSim/At/CutTie.lean.
Johnson/SendSim/At/RowsExact.lean and Johnson/SendSim/At/RowsFresh.lean apply the two implications
to theorems, which gives rowsExact and rowsFresh. rowsFreshAny_of_core is in
Johnson/SendSim/At/FoldAnyRoad.lean.

Notes: what the proofs use besides the premises. All of it is proved. Pointwise: withinOf
(Johnson/SendSim/At/Within.lean), mends_paid and shown_paid (Johnson/SendSim/At/Paid.lean),
mendsOffOf (Johnson/SendSim/At/ClearOfFold.lean), spentTie and knownTie
(Johnson/SendSim/At/CutProof.lean). On distributions, only general lemmas on probability:
nothingSpent (Johnson/SendSim/At/NothingSpent.lean), where the address spends nothing; that the
image of an image is the image under the composite; and that two maps that take uniform to uniform
do so side by side (map_unif_prodMap, Prob/Linear.lean).
-/
import Johnson.SendSim.At.CutProof
import Johnson.SendSim.At.Within
import Johnson.SendSim.At.NothingSpent

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

/-- The image of a distribution under a composite of three functions, one function at a time. -/
theorem map3 {α β γ δ : Type} (p : PMF α) (f : α → β) (g : β → γ) (h : γ → δ) :
    p.map (fun a => h (g (f a))) = ((p.map f).map g).map h := by
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- Spec.sendExact and Spec.readUnif imply Spec.rowsExact. The premises are proved as sendExact in
Johnson/SendSim/CoreProofs.lean and as readUnif in Johnson/SendSim/At/ReadUnif.lean. -/
theorem rowsExact_of_core (hE : Spec.sendExact) (hU : Spec.readUnif) : Spec.rowsExact := by
  intro P first ride data data' ds asks hf hs hβ hb
  obtain ⟨back, hback⟩ := shown_paid P first ride ds asks hf hs hβ
  have e : ∀ dat, shownR P first ride dat ds asks = fun c =>
      back ((sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride dat)
        (readC P ride c)) := fun dat => funext fun c => hback dat c
  rw [e data, e data', map3, map3, hU P ride hf,
    hE GF (sender P ride) (wOf P ds) (asksOf P asks) (dataOf P ride data) (dataOf P ride data')
      (withinOf P ride asks hf hb) (mends_paid P ride ds hf hs hβ)]

open Classical in
/-- The step that rowsFresh_of_core and rowsFreshAny_of_core share. Given Spec.sendFresh,
Spec.readUnif and the four premises of Spec.rowsExact, suppose that MendsOff holds at the instance
for the sets of spent and known names, and that bs satisfies SpentBack and maps uniform values to
uniform runs. Then the equation of Spec.rowsFresh holds. The condition on the spender (SpenderClear)
is not among the premises: this is a tool for the two proofs that call it, not a result of its own.
-/
theorem fresh_leg (hFr : Spec.sendFresh) (hU : Spec.readUnif) (P : K1.Par) (first : Nat)
    (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr)
    (hf : sendFits P ride = true) (hs : seedsFit P ds = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) (hb : budAt P asks)
    (hM : (sender P ride).MendsOff (wOf P ds) (spentN P ride Bk o p) (knownN P ride Bk ord o p)
      (knownT P ride Bk ord o p))
    (bs : (↥(spentN P ride Bk o p) → GF) → CsAll ((Bk.spentBy o p).map Ahead.named))
    (hbs : SpentBack P ride Bk o p bs)
    (hbu : (unif (↥(spentN P ride Bk o p) → GF)).map bs =
      unif (CsAll ((Bk.spentBy o p).map Ahead.named))) :
    (unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), shownR P first ride data ds asks c,
          cutAll c (Bk.knownBy ord o p))) =
      (unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 (Bk.knownBy ord o p)) := by
  obtain ⟨bk, hbk⟩ := knownTie P ride Bk ord o p
  obtain ⟨back, hback⟩ := shown_paid P first ride ds asks hf hs hβ
  have hcore := hFr GF (sender P ride) (wOf P ds) (asksOf P asks) (dataOf P ride data)
    (spentN P ride Bk o p) (knownN P ride Bk ord o p) (knownT P ride Bk ord o p)
    (withinOf P ride asks hf hb) hM
  -- T maps the instance's four components to the triple of the equation
  obtain ⟨T, hT⟩ : ∃ T : (↥(spentN P ride Bk o p) → GF) × (List GF × (AnsN P → GF)) ×
      (↥(knownN P ride Bk ord o p) → GF) × (↥(knownT P ride Bk ord o p) → GF) →
      Option (CsAll ((Bk.spentBy o p).map Ahead.named)) × List Shown ×
        Option (CsAll ((Bk.knownBy ord o p).map Ahead.named)),
      T = fun z => (some (bs z.1), back z.2.1, bk (z.2.2.1, z.2.2.2)) := ⟨_, rfl⟩
  -- F1, F2: the instance's four components, on the two sides of Spec.sendFresh
  obtain ⟨F1, hF1⟩ : ∃ F1 : (sender P ride).Coins → (↥(spentN P ride Bk o p) → GF) ×
      (List GF × (AnsN P → GF)) × (↥(knownN P ride Bk ord o p) → GF) ×
      (↥(knownT P ride Bk ord o p) → GF),
      F1 = fun c' => ((sender P ride).cut (spentN P ride Bk o p) c',
        (sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data) c',
        (sender P ride).cut (knownN P ride Bk ord o p) c',
        (sender P ride).cutT (knownT P ride Bk ord o p) c') := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : (↥(spentN P ride Bk o p) → GF) × (sender P ride).Coins →
      (↥(spentN P ride Bk o p) → GF) × (List GF × (AnsN P → GF)) ×
      (↥(knownN P ride Bk ord o p) → GF) × (↥(knownT P ride Bk ord o p) → GF),
      F2 = fun a => (a.1,
        (sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data) a.2,
        (sender P ride).cut (knownN P ride Bk ord o p) a.2,
        (sender P ride).cutT (knownT P ride Bk ord o p) a.2) := ⟨_, rfl⟩
  have hcore' : (unif (sender P ride).Coins).map F1 =
      (unif ((↥(spentN P ride Bk o p) → GF) × (sender P ride).Coins)).map F2 := by
    rw [hF1, hF2]
    convert hcore
  -- the left side of the equation
  have eL : (fun c : Cs (dueR P ride) => (cutAll c (Bk.spentBy o p),
      shownR P first ride data ds asks c, cutAll c (Bk.knownBy ord o p))) =
      fun c => T (F1 (readC P ride c)) := by
    funext c
    rw [hT, hF1, hbs c, hback data c, hbk c]
  -- G: the common form of both sides
  obtain ⟨G, hG⟩ : ∃ G : CsAll ((Bk.spentBy o p).map Ahead.named) × (sender P ride).Coins →
      Option (CsAll ((Bk.spentBy o p).map Ahead.named)) × List Shown ×
        Option (CsAll ((Bk.knownBy ord o p).map Ahead.named)),
      G = fun z => (some z.1,
        back ((sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data) z.2),
        bk ((sender P ride).cut (knownN P ride Bk ord o p) z.2,
          (sender P ride).cutT (knownT P ride Bk ord o p) z.2)) := ⟨_, rfl⟩
  have eR : (fun a : CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride) =>
      (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 (Bk.knownBy ord o p))) =
      G ∘ fun a => (id a.1, readC P ride a.2) := by
    funext a
    rw [hG]
    show _ = (some a.1, back _, bk _)
    rw [hback data a.2, hbk a.2]
  have eM : T ∘ F2 = G ∘ fun a => (bs a.1, id a.2) := by
    funext a
    rw [hT, hG, hF2]
    rfl
  rw [eL, map3 (unif _) (readC P ride) F1 T, hU P ride hf, hcore', PMF.map_comp, eM,
    ← PMF.map_comp,
    map_unif_prodMap bs id hbu (PMF.map_id _), eR,
    ← PMF.map_comp, map_unif_prodMap id (readC P ride) (PMF.map_id _) (hU P ride hf)]

open Classical in
/-- Spec.sendFresh, Spec.readUnif and Spec.spentUnif imply Spec.rowsFresh. The premises are proved
as sendFresh in Johnson/SendSim/CoreProofs.lean, as readUnif in Johnson/SendSim/At/ReadUnif.lean and
as spentUnif in Johnson/SendSim/At/SpentUnif.lean. -/
theorem rowsFresh_of_core (hFr : Spec.sendFresh) (hU : Spec.readUnif) (hSU : Spec.spentUnif) :
    Spec.rowsFresh := by
  intro P first ride data ds asks Bk ord o p hf hs hβ hb hW hSC
  rcases hSC with h0 | h
  · exact nothingSpent _ _ _ _ _ _ h0
  · obtain ⟨bs, hbs⟩ := spentTie P ride Bk ord o p hf hW h
    exact fresh_leg hFr hU P first ride data ds asks Bk ord o p hf hs hβ hb
      (mendsOffOf P ride ds Bk ord o p hf hs hβ h) bs hbs (hSU P ride Bk ord o p hf hW h bs hbs)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rowsFresh_of_core
#print axioms OnBytes.SendSim.At.rowsExact_of_core
