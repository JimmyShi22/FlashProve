-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TotalMoves.lean: THE FIELD `htin` OF `TableOwes`
(Johnson/Desc/First/Link/Law/LinkTable.lean: behind the frame's move the one sum can be taken on the
own rows), IN ITS OWN TYPE. Theorems: joinings of TotalBehind.lean, SeatsRide.lean, TotalAlong.lean,
SizedRides.lean and GoodFull.lean. No text already in the library turns.

  `runBehind_of_moves`: a yes of the one move of the frame's sub-protocol behind the batching
    (`moves₂`) is a yes of `Link.runBehind`.
  `rs_runBehind`, `holds_runBehind`: what every run of the order behind the batching keeps passes a
    yes of `Link.runBehind`.
  `totalIn_moves`: the public test behind that move, FROM WHAT HOLDS IN FRONT OF IT: the state is
    "good" (a part is there; the draw has run; a sum a slot); the ledger has its sizes, a sum a slot
    and the looks sh; the mask row's message is seated and each array below sh's length is there;
    `SortsAt sh`: the test `sortsB sh` says yes of THE STATE's OWN structure of the range proof.
  `htin_of`: **THE FIELD, TO THE LETTER: ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map
    (·.move)) a.1 t [] → K9.totalIn own t = true**, where on1 gives these four at a.1.
  `sorts_blank`, `rests_sorts`: **`SortsAt sh` passes each of the nine known runs**: the test reads
    none of the fourteen fields that the equations' run writes.
  ITS OTHER PREMISES: the runs' share, four times (every run of the order behind the batching keeps
    "good", hands on `SizedLooks sh`, stands in `Rs`, hands on `SortsAt sh`: at the known runs
    `rests_good`, `rests_fork (sizedLooks_rests sh)`, `runRests_of_rel rests_rs`, `rests_sorts sh`)
    · the order ends
    in an entry whose run stands under `k8Tests nU`.
`sortsB sh tl` is not asked of EVERY state with such a ledger and any
structure tl: nothing would pin tl, so that premise would be false as soon as one such state is
there, and `htin_of` true only where empty.
Limits. AN IMPLICATION: none of the premises is shown of a link here. h1 is shown of no state: on1
must bear «reached», the open link's number (one sh for all of on1) and the plan's structure of the
range proof; `SortsAt` has no payer between «opened» and on1: `rests_sorts` covers the RUNS; the
sub-protocols' STEPS write that structure too, and no walk over them is typed. Nothing on soundness.


-/
import Johnson.Desc.First.Link.Law.TotalAlong
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.TailClaims.EquationsBlank
import Johnson.Desc.First.K8.LawAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.K9 (atS totalIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- A yes of the one move behind the batching is a yes of the runs behind it. -/
theorem runBehind_of_moves {α : Type} (L : Link S Claim) (s t : S) (cls : List Claim)
    (h : MovesYes atS ((moves₂ (α := α) L).map (·.move)) s t cls) : L.runBehind s = .ok t := by
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := h
  exact hq

/-- What every run of the order behind the batching keeps passes a yes of these runs. -/
theorem holds_runBehind (Pp : S → Prop) (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Pp e → Pp e₁)
    (s t : S) (h : L.runBehind s = .ok t) (hs : Pp s) : Pp t :=
  ran_holds Pp L.hear L.orderAfter _ _
    (afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind h))
    (fun o ho run hl x x₁ hr hx => hk o ho run hl x x₁ hr hx) hs

theorem rs_runBehind (L : Link S Claim)
    (hk : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (s t : S) (h : L.runBehind s = .ok t) : Rs s t :=
  holds_runBehind (Rs s) L (fun o ho run hl e e₁ hr hx => hx.trans (hk o ho run hl e e₁ hr)) s t h
    (Rs.refl s)

/-- The test on the looks and the planned numbers says yes of the state's own structure. -/
def SortsAt (sh : List Look) (s : S) : Prop := ∀ tl, s.tl? = some tl → sortsB sh tl = true

/-- The test reads none of the fourteen fields that are blanked. -/
theorem sorts_blank (sh : List Look) (u tl : HTailF2) :
    sortsB sh (First.TailClaims.Law.blank u tl) = sortsB sh tl := rfl

theorem sortsAt_same {sh : List Look} {s s' : S} (h : s'.tl? = s.tl?) :
    SortsAt sh s → SortsAt sh s' := fun k tl htl => k tl (h ▸ htl)

theorem sortsAt_putTl {sh : List Look} {s : S} {tl tl' : HTailF2} (u : HTailF2)
    (h : s.tl? = some tl)
    (hb : First.TailClaims.Law.blank u tl' = First.TailClaims.Law.blank u tl) :
    SortsAt sh s → SortsAt sh (s.putTl tl') := by
  intro k x hx
  rw [First.K8.putTl_tl s tl tl' h] at hx
  obtain rfl := Option.some.inj hx
  rw [← sorts_blank sh u, hb, sorts_blank]
  exact k tl h

theorem tl_putFork' (s : S) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, S.tl?, ho]
  | _ => rfl

open OnBytes.Desc.First.K4 (frontAtC_pays backAtC_pays) in
open VerifiableInference.Desc.First.MergeLaw (claim_inv) in
open VerifiableInference.Desc.K4Run in
open VerifiableInference.Desc.Kinds.Head.Law (join_hands) in
/-- **THE NINE KNOWN RUNS.** -/
theorem rests_sorts (sh : List Look) : RunRests fun e e₁ => SortsAt sh e → SortsAt sh e₁ where
  refl _ := id
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, ⟨h1, rfl⟩, _⟩ := frontAtC_pays h0 hr
    exact sortsAt_same (by simp [S.tl?, h1])
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, ⟨h1, rfl⟩, _⟩ := backAtC_pays h0 hr
    exact sortsAt_same (by simp [S.tl?, h1])
  free p r h0 e e₁ hr := by
    obtain ⟨a, ⟨h1, rfl⟩⟩ := k4_freeSlot_wrote h0 hr
    exact sortsAt_same (by simp [S.tl?, h1])
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, _⟩ := claim_inv hr
    exact sortsAt_same (by simp [S.tl?, h1])
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact sortsAt_same (by simp [S.tl?, h1])
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, _, htl, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    exact fun k => sortsAt_same (tl_putFork' _ _)
      (sortsAt_putTl tl htl (First.TailClaims.Law.eq_blank tl he) k)
  ls e e₁ hr := by
    obtain ⟨F, tl, _, htl, rfl⟩ := k8LsTail_ok e e₁ hr
    exact sortsAt_putTl tl htl (First.TailClaims.Law.blank_lsTail tl tl _)
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, _, htl, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    exact fun k => sortsAt_same (tl_putFork' _ _) (sortsAt_putTl tl htl rfl k)

/-- **The public test behind the frame's move, from what holds in front of it.** -/
theorem totalIn_moves (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ) (L : Link S Claim)
    (g2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      good9 e → good9 e₁)
    (k2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (r2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (q2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      SortsAt sh e → SortsAt sh e₁)
    (s t : S) (h : L.runBehind s = .ok t) (hg : good9 s) (hl : HasFork (SizedLooks sh) s)
    (hseat : SeatsThere own sh.length s) (hso : SortsAt sh s) : totalIn own t = true := by
  obtain ⟨a, ha, _, _⟩ := holds_runBehind good9 L g2 s t h hg
  obtain ⟨G, hG, ⟨hS, hLS⟩, _⟩ := holds_runBehind (HasFork (SizedLooks sh)) L k2 s t h hl
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans (fork_part t a ha))
  obtain ⟨t2, t3⟩ := seats_ride own sh.length (rs_runBehind L r2 s t h) a ha hseat
  obtain ⟨e, he, ht⟩ := full_runBehind (fun x => HasFork (SizedLooks sh) x ∧ SortsAt sh x) nU L pre
    oT hord hT
    (fun o' ho' run hr x x₁ hx hp =>
      ⟨k2 o' (by rw [hord]; exact List.mem_append_left _ ho') run hr x x₁ hx hp.1,
        q2 o' (by rw [hord]; exact List.mem_append_left _ ho') run hr x x₁ hx hp.2⟩) s t h
    ⟨hl, hso⟩
  obtain ⟨⟨Fe, hFe, _, hle⟩, hse⟩ := he
  exact totalIn_tests sh own nU e t a ht ha ⟨Fe, hFe, hle⟩ hse ⟨hLS, hS.1, hS.2.1⟩ t2 t3

/-- **THE FIELD htin OF TableOwes, TO THE LETTER.** -/
theorem htin_of {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    (L : Link S Claim) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (g2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      good9 e → good9 e₁)
    (k2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (r2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (q2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      SortsAt sh e → SortsAt sh e₁) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true := fun a t ha hy =>
  totalIn_moves sh own nU L g2 k2 r2 pre oT hord hT q2 a.1 t
    (runBehind_of_moves (α := α) L a.1 t [] hy) (h1 a ha).1 (h1 a ha).2.1 (h1 a ha).2.2.1
    (h1 a ha).2.2.2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.runBehind_of_moves
#print axioms VerifiableInference.Desc.LinkJoin.holds_runBehind
#print axioms VerifiableInference.Desc.LinkJoin.rs_runBehind
#print axioms VerifiableInference.Desc.LinkJoin.rests_sorts
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_moves
#print axioms VerifiableInference.Desc.LinkJoin.htin_of
