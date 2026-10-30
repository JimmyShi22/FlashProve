-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeyRide15.lean. THE TABLE OF JOINTS OF THE KEY FILE, ROW
1.15 (the proximity test on the lookups' own message, at border 15 of the first chain): THE RIDERS
OF ITS CLAIM's HALF: the six items that are open in front of the test and that it does not close
hold in front, AT THE WITNESS WITH MESSAGE 1 LAID, if they hold behind. Statements with proofs.
ride_15 is the premise "ride" of relAt_back_to (Johnson/RunOne/Law/KeyQuietSub.lean) at that row.
OBJECT. KItem.holds at meaning₁At, at the six: unmarked, pinT, pin 0, srow 0, kclaims 0, kclaims 1.
USER. The row's "back" (K12GivesHalves.lean). K12Back15.lean imports this file.
LETTERS. The description F, the reading G, the seats at_, the reader R, the ring's reading ρ, the
two records a (in front) and b (behind), the strings y and y', the witness w, THE LAID TABLE m
(any).

What a row reads, and the tools that are general in the laid messages, stand in
Johnson/RunOne/Law/KeyRideTools.lean; ride_srow0 is a call of ride_srowAt there; valOf_layG
there is what the proofs below call.
THE RIDERS:
  ride_srow0        message 0's sample rows, at the letters K R X.
  ride_kclaims      a lookup's claims on its keys, at the letters K R X: from hmask: each claim's
                    mask form READS at the laid witness as at w: only the use.
  hmask_of_ledger   its first payer: every slot names message 0 (K13.Law.OnLedger).
  hmask_of_read     its second: a slot may name another message with a coefficient that reads 0.
  open15, six15,    the open set at border 15, the six, and what the table's row closes and lays
                    there: by
  row15             evaluation in the kernel.
  ride_15           all six.
  back_15           THAT IT FITS: the row's claim's half from its law (not paid here) and the
                    riders, by one call of relAt_back_to.
WHICH PREMISE EACH OF THE SIX SPENDS. unmarked: none (the readers' "marked" is constantly false).
pinT: hrec, Hy.cell. pin 0: hsmp, Hy.word, ha, hs. srow 0: hS, h0, hin, hsame, ha, hr, hs. kclaims
0 and 1: hkeys, hmask, hsame.
Limits. RULES: AS EMPTY AS THEIR PREMISES. No block is shown to have them.
(Where this and lean/THEOREM.md differ, the page holds.) hmask, in any of its
three forms, stands in no promise of the table before border 17. hin, ha and hr stand in the
promise at border 15. No member of the row's guard is shown. Nothing on soundness; nothing on
hiding.

-/
import Johnson.RunOne.KeyRows1At
import Johnson.Desc.K13.Law.Agree
import Johnson.RunOne.Law.KeyQuietSub
import Johnson.RunOne.Law.KeyRideTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.KeyRide15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.Law.KeyRideTools

/-! ## 1 The ties at this row -/

/-- Message 1 is laid; message 0 rides. -/
theorem ties15 {A Cells M Smp Rec : Type} {G : Reading A Cells M Smp Rec} {at_ : Where}
    {R : KRead Cells M} (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0])
    (hs : SeatsApart at_ [1] [0]) : LayTies G at_ R [1] [0] :=
  ⟨ha, hr, by simp, hs⟩

/-! ## 2 The riders, at the letters -/

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)
variable {P S Cells M Smp Rec : Type} (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop)
  (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

local notation "Mg" => meaning₁ K R X near forms worth other

/-- **Message 0's sample rows ride.** -/
theorem ride_srow0 (a b : P × S) (y y' : Strs) (w : Wit Cells Unit M) (m : M)
    (hS : K1.SmpStay (X.st a.2) (X.st b.2))
    (h0 : ∀ o, K.orc 0 = some o → ∃ x, (X.st a.2).oracles[o]? = some x ∧ x.sampled = true)
    (hin : ∀ o, K.orc 0 = some o → KeyRows23.SampleIn (X.st a.2) o)
    (hnum : ∀ o, K.orc 0 = some o → ∀ k, K.num o = some k → k = 0)
    (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0])
    (hu : (Mg).srow 0 b y' w) : (Mg).srow 0 a y (layAt at_ [1] (fun _ => m) w) := by
  exact ride_srowAt K (fun _ => m) w ρ (ties15 ha hr hs) hsame (X.st a.2) (X.st b.2) 0 hS h0 hin
    (fun o ho j hj => by rw [hnum o ho j hj]; simp) hu

/-- **A lookup's claims on its keys ride.** hmask: ONLY THE USE, READ: each claim's mask form reads
at
the laid witness as at w. -/
theorem ride_kclaims (l : Nat) (a b : P × S) (y y' : Strs) (w : Wit Cells Unit M) (m : M)
    (hkeys : X.keysAt b.2 l = X.keysAt a.2 l)
    (hmask : ∀ ks, X.keysAt a.2 l = some ks → ∀ x ∈ ks,
      ρ.val (formAt (mkOf K R (layAt at_ [1] (fun _ => m) w)) x.masks) =
        ρ.val (formAt (mkOf K R w) x.masks))
    (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (hu : (Mg).kclaims l b y' w) : (Mg).kclaims l a y (layAt at_ [1] (fun _ => m) w) := by
  obtain ⟨L, ks, h1, h2, h3, h4⟩ := hu
  have h2a : X.keysAt a.2 l = some ks := hkeys.symm.trans h2
  refine ⟨L, ks, h1, h2a, h3, fun x hx => ?_⟩
  have hb := h4 x hx
  unfold TensorRowHolds at hb ⊢
  rw [hsame] at hb ⊢
  beta_reduce at hb ⊢
  rw [ρ.add] at hb ⊢
  rw [hmask ks h2a x hx]
  exact hb

/-- **hmask's first payer**: the list form: every slot names the message idx, which is message 0 or
no
component: then the two mask forms are one word. -/
theorem hmask_of_ledger (idx : Nat) (w : Wit Cells Unit M) (m : M) (x : TensorRow)
    (hx : K13.Law.OnLedger idx x) (hidx : ∀ k, K.num idx = some k → k = 0)
    (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0]) :
    ρ.val (formAt (mkOf K R (layAt at_ [1] (fun _ => m) w)) x.masks) =
      ρ.val (formAt (mkOf K R w) x.masks) :=
  congrArg ρ.val (formAt_reads _ _ _ fun q hq => by
    unfold mkOf
    rw [hx q hq, valOf_layG K (fun _ => m) w (ties15 ha hr hs) idx
      (fun k hk => by rw [hidx k hk]; simp)])

/-- **hmask's second payer**: a slot may name another message with a coefficient that reads 0. -/
theorem hmask_of_read (w : Wit Cells Unit M) (m : M) (x : TensorRow)
    (hx : ∀ q ∈ x.masks, (∀ k, K.num q.1.oracle = some k → k = 0) ∨ ρ.val q.2 = 0)
    (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0]) :
    ρ.val (formAt (mkOf K R (layAt at_ [1] (fun _ => m) w)) x.masks) =
      ρ.val (formAt (mkOf K R w) x.masks) :=
  formAt_read_congr ρ _ _ _ fun q hq => (hx q hq).imp
    (fun hn => by
      unfold mkOf
      rw [valOf_layG K (fun _ => m) w (ties15 ha hr hs) q.1.oracle
        (fun k hk => by rw [hn k hk]; simp)])
    id

end

/-! ## 3 Row 1.15 -/

/-- What is open at border 15. -/
theorem open15 : open₁ 2 15 =
    [.unmarked, .pinT, .pin 0, .srow 0, .pin 1, .kclaims 0, .kclaims 1, .grows] := by
  decide

/-- **The six**: what is open there and is not closed by the row. -/
theorem six15 : (open₁ 2 15).filter (· ∉ [KItem.grows, KItem.pin 1]) =
    [.unmarked, .pinT, .pin 0, .srow 0, .kclaims 0, .kclaims 1] := by
  decide

/-- The table's row there closes just these two, reads and leaves none, and lays message 1. -/
theorem row15 : ((rows₁ 2)[15]?).map (fun r => (r.ins, r.ctx, r.lays)) =
    some ([KItem.grows, KItem.pin 1], [], [1]) := by
  decide

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where) (one : OneTime) (R : KRead Cells M)

/-- **Row 1.15's riders.** a: the record in front of the test; b: behind. m: ANY table. -/
theorem ride_15 (a b : Xi × FirstState) (y y' : Strs) (w : Wit Cells Unit M) (m : M)
    (Hy : StrsStay F at_ (open₁ 2 15) y y')
    (hrec : G.recOf b = G.recOf a)
    (hsmp : G.smp b (at_ 0).1 (at_ 0).2 = G.smp a (at_ 0).1 (at_ 0).2)
    (hS : K1.SmpStay a.2.d.st b.2.d.st)
    (h0 : ∃ x, a.2.d.st.oracles[0]? = some x ∧ x.sampled = true)
    (hin : KeyRows23.SampleIn a.2.d.st 0)
    (hkeys : ∀ l, l < 2 → (readers₁ one).keysAt b.2 l = (readers₁ one).keysAt a.2 l)
    (hmask : ∀ l ks, l < 2 → (readers₁ one).keysAt a.2 l = some ks → ∀ x ∈ ks,
      ρ.val (formAt (mkOf (plan₁ one) R (layAt at_ [1] (fun _ => m) w)) x.masks) =
        ρ.val (formAt (mkOf (plan₁ one) R w) x.masks))
    (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0]) :
    ∀ i ∈ open₁ 2 15, i ∉ [KItem.grows, KItem.pin 1] → i.holds F G at_ (meaning₁At one R) b y' w →
      i.holds F G at_ (meaning₁At one R) a y (layAt at_ [1] (fun _ => m) w) := by
  intro i hi hn hu
  have ho0 : ∀ o, (plan₁ one).orc 0 = some o → o = 0 := fun o ho => by
    simpa [plan₁, KeyReaders.planOf] using ho.symm
  have hn0 : ∀ k, (plan₁ one).num 0 = some k → k = 0 := fun k hk => by
    simpa [plan₁, KeyReaders.planOf] using hk.symm
  have hp0 : KItem.pin 0 ∈ open₁ 2 15 := by rw [open15]; simp
  rw [open15] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · exact pinT_of_cells G a y w _ rfl (rides_pinT2_at G a b y y' w hrec Hy.cell hu)
  · exact ride_pinG F (fun _ => m) (ties15 ha hr hs) 0 (by simp) a b y y' w hsmp
      (Hy.word 0 (mem_pinned _ 0 hp0)) hu
  · exact ride_srow0 ρ G at_ (plan₁ one) R (readers₁ one) _ _ _ _ a b y y' w m
      hS (fun o ho => by rw [ho0 o ho]; exact h0) (fun o ho => by rw [ho0 o ho]; exact hin)
      (fun o ho k hk => hn0 k (by rw [ho0 o ho] at hk; exact hk)) hsame ha hr hs hu
  · exact absurd (by simp) hn
  · exact ride_kclaims ρ at_ (plan₁ one) R (readers₁ one) _ _ _ _ 0 a b y y' w m
      (hkeys 0 (by decide)) (fun ks => hmask 0 ks (by decide)) hsame hu
  · exact ride_kclaims ρ at_ (plan₁ one) R (readers₁ one) _ _ _ _ 1 a b y y' w m
      (hkeys 1 (by decide)) (fun ks => hmask 1 ks (by decide)) hsame hu
  · exact absurd (by simp) hn

/-- **That it fits**: the claim's half of row 1.15 from the row's law and these riders, by one call
of relAt_back_to. r: the table's row there, said by its two lists (row15). law: the closed items at
the laid witness: NOT PAID HERE. -/
theorem back_15 (r : KRow) (hins : r.ins = [KItem.grows, KItem.pin 1]) (hctx : r.ctx = [])
    (a b : Xi × FirstState) (y y' : Strs) (w : Wit Cells Unit M) (m : M)
    (Hy : StrsStay F at_ (open₁ 2 15) y y')
    (hrec : G.recOf b = G.recOf a)
    (hsmp : G.smp b (at_ 0).1 (at_ 0).2 = G.smp a (at_ 0).1 (at_ 0).2)
    (hS : K1.SmpStay a.2.d.st b.2.d.st)
    (h0 : ∃ x, a.2.d.st.oracles[0]? = some x ∧ x.sampled = true)
    (hin : KeyRows23.SampleIn a.2.d.st 0)
    (hkeys : ∀ l, l < 2 → (readers₁ one).keysAt b.2 l = (readers₁ one).keysAt a.2 l)
    (hmask : ∀ l ks, l < 2 → (readers₁ one).keysAt a.2 l = some ks → ∀ x ∈ ks,
      ρ.val (formAt (mkOf (plan₁ one) R (layAt at_ [1] (fun _ => m) w)) x.masks) =
        ρ.val (formAt (mkOf (plan₁ one) R w) x.masks))
    (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0])
    (law : (∀ i ∈ r.outs ++ r.ctx, i.holds F G at_ (meaning₁At one R) b y' w) →
      ∀ i ∈ r.ins, i.holds F G at_ (meaning₁At one R) a y (layAt at_ [1] (fun _ => m) w))
    (h : relAt F G at_ (meaning₁At one R) (stepOpen (open₁ 2 15) r) b y' w) :
    relAt F G at_ (meaning₁At one R) (open₁ 2 15) a y (layAt at_ [1] (fun _ => m) w) :=
  KeyQuietSub.relAt_back_to F G at_ (meaning₁At one R) r (open₁ 2 15) a b y y' w _
    (by rw [hctx]; simp) law
    (by
      rw [hins]
      exact ride_15 ρ F G at_ one R a b y y' w m Hy hrec hsmp hS h0 hin hkeys hmask hsame ha hr hs)
    h

end

end Johnson.RunOne.Law.KeyRide15

#print axioms Johnson.RunOne.Law.KeyRide15.ride_srow0
#print axioms Johnson.RunOne.Law.KeyRide15.ride_kclaims
#print axioms Johnson.RunOne.Law.KeyRide15.hmask_of_ledger
#print axioms Johnson.RunOne.Law.KeyRide15.hmask_of_read
#print axioms Johnson.RunOne.Law.KeyRide15.open15
#print axioms Johnson.RunOne.Law.KeyRide15.six15
#print axioms Johnson.RunOne.Law.KeyRide15.row15
#print axioms Johnson.RunOne.Law.KeyRide15.ride_15
#print axioms Johnson.RunOne.Law.KeyRide15.back_15
