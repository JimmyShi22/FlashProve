-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Front.lean: the merge's law at a piece, joined with its run's, under fewer
premises. Definitions, and theorems with their proofs.

Against `merge_closed_leads` and `closed_run` (Closed.lean, ClosedRun.lean): (1) the two are joined
under one "the prover has lost"; (2) the clause "the first of the sumcheck's own slots is the
ledger's next free slot" leaves the condition in front: it follows from the yes; (3) the place's
layout is asked to be the block's, not its number of column bits alone; (4) the written rounds are
no letters under `MergeDs` any more: they are any list with the block's own entries; (5) the entries
m are read off the statement in front, as the typed statement is; (6) the written counts are held
against 2⁻¹ ^ 128.

Main names:
  `next_of_yes`: where the merge says yes, the ledger's next free slot in front, and 2 lk + 3, is
  the
    plan's number of slots: the merge takes 2 lk + 3 slots and then holds the next free slot against
    that number.
  `FrontReads`: the condition in front: the typed statement is read off the record (its ledger, its
    claim), and the slot of the claim's value is the number's. `frontIs_of_yes`: on a yes it gives
    `FrontIs`, where N.first + 2 lk + 3 is the plan's number of slots.
  `RunSays`: the conclusion of `closed_run`, as a definition.
  `merge_run_leads`: for every reader m of the entries off the statement in front:
    `Reduction.Leads` of the piece's reduction, on the statements with `FrontReads` whose ledger's
    arrays have their size, towards `ClosedSays`
    and `RunSays`. Where `FrontIs` fails in front the block never says yes.
  `mergeWr_of_entries`: what the bound on the written counts asks of the rounds, out of the entries.
  `merge_law`: the same at any list of written rounds whose entries are `mergeEntries`, each round
  of
    the kind of its entry's name (Johnson/Top/H0/MergeLaw/AtEntries.lean); and the piece's errors
    are
    shares of at most 2⁻¹ ^ 128 of each round's written challenges (`merge_written`,
    Johnson/Top/H0/MergeLaw/Written.lean).

WHAT STAYS A PREMISE OF `merge_law`, ONE BY ONE. On public numbers: the place's layout is the
block's;
the place has one claim; N.first + 2 lk + 3 is the plan's number of slots; the written rounds have
the block's entries and their names' kinds. In front: `FrontReads`; the ledger's three arrays have
one entry for each slot. Inside `RunSays`: between the merge and its run the ledger only grows later
and what the merge left stays in the record; the run says yes; the last ledger is later than the
run's; Rd; the run's claim is worth 0 in the last ledger's world at the entries' mask row; the row
on
the end value. Letters: the place Pl and the numbers N (tied to the block and to the record by the
equations named), Rd, rd, m, base, ext, the frame F, the type W. That m reads what the statement's
oracles decode to, and that a border's relation says so of its witness (the pin), is not said here.
That the typed claim is the table's item on the weights, and the row on the end value its item on
what the merge left (Johnson/Top/H0/K11Caller/Items.lean: `weightsSays_iff`, `woSays_iff`), is
called
nowhere here; no theorem ties the pending rows to the row that the link's end lays.

Limits. It is no soundness of the protocol. A bound on each round, not on a sum over rounds. Nothing
on hiding.

-/
import Johnson.Top.H0.MergeLaw.ClosedRun
import Johnson.Top.H0.MergeLaw.AtEntries
import Johnson.Top.H0.MergeLaw.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE oneE subE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World Fork wsForkStart)
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim headClaimMergeKind
    mergeEntries)
open OnBytes.Tie.Pv.Lay.Eng (sumOut)
open K11Caller (MergeIn GS Fits2 maskOf)
open _root_.Run (ckP)
open scoped ENNReal

/-- **Where the merge says yes, the ledger's next free slot in front is fixed by the plan's number
of slots**: the merge takes 2 lk + 3 slots and then holds the next free slot against that number. -/
theorem next_of_yes {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok
           s')
    (a : HeadOwn) (ha : s.here = .head a) : a.F.next + 1 + 2 * P.lay.lk + 2 = P.nMsg := by
  obtain ⟨a0, _, _, F, _, _, _, ha0, _, _, _, _, _, hm, _, _, _, hnext⟩ := decide_inv h
  have e : a0 = a := by
    rw [ha] at ha0
    exact (Here.head.inj ha0).symm
  subst e
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhide, _⟩ := hear_ended hm
  obtain ⟨_, _, eF⟩ := hide_inv (hideRun_one hhide)
  rw [← hnext, eF]

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)
  (Rd : MergeIn Pl.n → (Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) → Prop)

/-- The condition in front without the clause on the next free slot: the typed statement is read off
the record (its ledger, its claim), and the slot of the claim's value is the number's. -/
def FrontReads (st : MergeIn Pl.n) (s : S) : Prop :=
  ∀ (a : HeadOwn) (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard), s.here = .head a
      → a.claim = some claim → a.x = some x0 →
    st.F = a.F ∧ (∀ i, st.cl i = claim) ∧ N.svA = #[x0.sV]

/-- On a yes the whole condition holds, where the first of the own slots is the plan's. -/
theorem frontIs_of_yes {P : HeadMergeP} (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg) {st :
    MergeIn Pl.n} {s s' : S}
    {rs : List Fmt.RoundView} (hf : FrontReads N st s) (h : headMergeDecide P s rs = .ok s') : FrontIs N st
        s := by
  intro a claim x0 ha hcl hx
  obtain ⟨f1, f2, f3⟩ := hf a claim x0 ha hcl hx
  have := next_of_yes h a ha
  exact ⟨f1, f2, f3, by omega⟩

/-- What the merge's yes says together with its run's: the conclusion of `closed_run`. -/
def RunSays (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) (st : MergeIn Pl.n) (s' : S) : Prop :=
  ∃ (a' : HeadOwn) (wo : OnBytes.Model.WsForkOut) (x mu cY beta v : E) (qs : List (Nat × List E ×
      E))
    (hβ : Reading.gl.val beta ≠ 0),
    s'.here = .head a' ∧ a'.wo = some wo ∧ wo.beta = beta ∧ wo.rm.toList = qs.map (·.2.2) ∧
    ∀ (n : ℕ) (s₂ s₃ : S) (a₂ a₃ : HeadOwn) (cls : List Claim) (Fl : Fork) (entry : ℕ → ℕ → ℕ → GE),
      s₂.here = .head a₂ → a₂.wo = a'.wo → Later a'.F a₂.F → headMergeClaim n s₂ = .ok (cls, s₃) →
      s₃.here = .head a₃ → Later a₃.F Fl →
      ∃ form, cls = [{ form := form }] ∧
        (Rd st m → form.value Reading.gl (Fl.worldOf Reading.gl (maskOf N m) entry) = 0 →
          (GS Reading.gl N Rd).L.f (st, Reading.gl.val x) m ((GS Reading.gl N Rd).L.toSum.Q.outPt
              (GS Reading.gl N Rd).L.toSum.M
              (sumOut Reading.gl (GS Reading.gl N Rd).L.toSum (fun st => pick ((GS Reading.gl N
                  Rd).L.toSum.T.par.vars st)) (st, Reading.gl.val x) wo.p.target mu
                wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)) =
            Reading.gl.val v - m (GS Reading.gl N Rd).L.cAt * Reading.gl.val beta →
          ∀ c, (GS Reading.gl N Rd).Cl st m c)

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, JOINED WITH ITS RUN's.** The entries are read off the statement in
front by m, a letter, as the typed statement is by rd. -/
theorem merge_run_leads (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = (GS Reading.gl N Rd).k) (H : MergeDs dZ d0 ds dY dV) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
    (rd : S × F.E.Str → MergeIn Pl.n) (m : S × F.E.Str → Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) :
    (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).ior.red.Leads
      (fun a => FrontReads N (rd a) a.1 ∧ ∀ b, a.1.here = .head b → OnBytes.PscRun.Sized b.F)
      (fun a a' => ClosedSays N Rd P (m a) (rd a) a.1 a'.1 ∧ RunSays N Rd (m a) (rd a) a'.1)
      (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).err := by
  have hlk : Pl.lay.lk = P.lay.lk := by rw [hlay]
  intro a ha
  by_cases hc : FrontIs N (rd a) a.1
  · refine Doomed.mono _ _ ?_ (merge_closed_leads N Rd P hk hlk h1 H base ext rd (m a) a hc)
    intro τ hτ a' ha'
    exact ⟨hτ a' ha', closed_run N Rd P hlk h1 (m a) (rd a) hc (hτ a' ha') ha.2⟩
  · refine Doomed.of_forall _ _ fun τ a' ha' => ?_
    obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
      (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext) rfl rfl a a' τ ha'
    exact absurd (frontIs_of_yes N hnum ha.1 hdec) hc

/-- What the bound on the written counts asks of the rounds (`MergeWr`,
Johnson/Top/H0/MergeLaw/Written.lean) follows from the block's own entries too. -/
theorem mergeWr_of_entries (k n work : ℕ) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (he : (dZ :: d0 :: (ds ++ [dY, dV])).map (·.entry) = mergeEntries k n work)
    (hkind : ∀ d ∈ dZ :: d0 :: (ds ++ [dY, dV]), d.kind ≠ .sealed ∧ d.kind ≠ .seeds) :
    MergeWr dZ d0 ds dY := by
  obtain ⟨eZ, e0, eR, eY, _, _⟩ := entries_of k n work he
  have one : ∀ (d : RDT) (e : Fmt.Entry), d.entry = e → e.drawE = 1 → e.drawNZ = 0 → e.poss = 0 →
      e.trits = 0 → e.logN ≤ 64 → d.kind ≠ .sealed ∧ d.kind ≠ .seeds → OneElem d := by
    intro d e h h1 h2 h3 h4 h5 hk
    subst h
    exact ⟨h1, h2, h3, h4, h5, hk.2, hk.1⟩
  have kY := hkind dY (by simp)
  refine ⟨one dZ _ eZ rfl rfl rfl rfl (Nat.zero_le _) (hkind dZ (by simp)),
    one d0 _ e0 rfl rfl rfl rfl (Nat.zero_le _) (hkind d0 (by simp)),
    fun d hd => one d _ (eR d hd) rfl rfl rfl rfl (Nat.zero_le _) (hkind d (by simp [hd])), ?_⟩
  exact ⟨by rw [eY], by rw [eY], by rw [eY], by rw [eY], by rw [eY]; exact Nat.zero_le _, kY.2,
    kY.1⟩

/-- **THE SAME AT ANY LIST OF WRITTEN ROUNDS THAT HAS THE BLOCK's OWN ENTRIES**, each round of the
kind of its entry's name; and its written counts are shares of at most 2⁻¹ ^ 128. -/
theorem merge_law (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N Rd).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (rd : S × F.E.Str → MergeIn Pl.n) (m : S × F.E.Str → Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE),
        (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => FrontReads N (rd a) a.1 ∧ ∀ b, a.1.here = .head b → OnBytes.PscRun.Sized b.F)
          (fun a a' => ClosedSays N Rd P (m a) (rd a) a.1 a'.1 ∧ RunSays N Rd (m a) (rd a) a'.1)
          (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, rfl⟩ := split_of_entries _ _ _ L he
  have hkind := kinds_of_names _ _ _ _ he hkd
  obtain ⟨H, hlen⟩ := mergeDs_of_entries _ _ _ he hkind
  have hk : ds.length = (GS Reading.gl N Rd).k := by
    show ds.length = Pl.lay.lk
    rw [hlen, hlay]
  have hn : (GS Reading.gl N Rd).n - 1 ≤ 2 ^ 62 := by
    show Pl.n - 1 ≤ 2 ^ 62
    rw [h1]
    exact Nat.zero_le _
  exact ⟨dZ, d0, ds, dY, dV, hk, rfl, fun base ext rd m =>
    ⟨merge_run_leads N Rd P hlay h1 hnum hk H base ext rd m,
      merge_written (GS Reading.gl N Rd) F.E hk H (mergeWr_of_entries _ _ _ he hkind) hn⟩⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_law
#print axioms VerifiableInference.Desc.First.MergeLaw.next_of_yes
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_run_leads
