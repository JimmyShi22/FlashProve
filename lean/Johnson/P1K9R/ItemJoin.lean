-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemJoin.lean: the batching kind's law (K9): TableOwes.hitems
(Johnson/Desc/First/Link/Law/LinkTable.lean), ONE ITEM's CLAUSE (ItemIn,
Johnson/Desc/First/Link/Law/HitemsStill.lean) AT AN ENTRY AT WHICH THE LINK STATES THE LOOKUP
ARGUMENT's RUN "join". One theorem and a small lemma; general in the lookup's accessors, in the
caller's keys and in the tables of terms. A law file: no sub-protocol imports it. After the pattern
of Johnson/P1K9R/ItemObjects.lean.
  refWorld_nil   without a window the kinds' laws' world (refWorld, K4Values.lean) is the ledger's
                 own (Fork.worldOf)
  item_join      THE CLAUSE: from: the entry is of the order, is not the approximate range proof's,
                 and the run "join" at these accessors and keys stands there; the accessors are the
                 verifier's state's own (AtS2) and fit (SeatFits); what the lookup has heard is read
                 off the fixed part; the table of terms there is plainTm (jnVals ..) at kv; and at
                 the statement: a part is there; the lookups' promise K3Ok holds of what is fixed;
                 the readers' second hole says nothing; the table's public test says yes; AND hkv:
                 each of the caller's key forms is worth kv in the world that the snapshot names
                 (refWorld at the part's ledger, no window, the entries entUnit)
HOW. run_of_reader: what the reader gives is the run's own claims' forms. join_heard, joinRun_cut
(Johnson/Top/H/K3RunsLaw.lean): a yes of "join" is ONE claim, of the form Fo.joinForm g KF, and the
state with one debt marked as paid: so no slot is late (lateOf_same). named_of_formsIn: the public
test says that every array which the join form names is named by the segment's list: so
value_meets_still (Johnson/Desc/First/Link/Law/WorldsMeet.lean): the form has one worth in the
table's world and in the snapshot's. There join_worth (at every later ledger, AT EVERY FUNCTION OF
ENTRIES) says the worth: Fo.claimJoin at the key forms' worths. SO THE MEETING OF THE TWO WORLDS IS
SPENT AT THE JOIN FORM ALONE, WHERE THE PUBLIC TEST PAYS IT: the key forms' own entries need not be
shown to be named.
LIMITS. An implication. The statement ends in ItemIn: an inclusion under "there are": what the one
form is stands in the proof alone. Whether K3Ok holds of what is fixed at a real state, whether the
public test says yes there, and hkv, are not shown here. No soundness is claimed.
-/
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.WorldsMeet
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Batch.Law.CoresTable
import Johnson.Top.H.Keep.RunsPlain
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.Keep.ReaderIsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K4Values (refWorld)
open VerifiableInference.OnPublicFiles (AtS2 SeatFits jnVals K3Ok pick_some pick_spec join_heard
        joinRun_cut join_worth keysOf lateOf_same fork_of_atS)

variable {α W : Type} {F : Frame}

/-- Without a window the kinds' laws' world is the ledger's own. -/
theorem refWorld_nil (U : Fork) (ent : ℕ → ℕ → ℕ → GQ) (y : Bound GQ) :
    refWorld Reading.gl U [] ent y = U.worldOf Reading.gl y.mask ent := by
  unfold refWorld Fork.worldOf
  congr 1

/-- **The clause at "join".** -/
theorem item_join (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (keys : S → Option (Array Aff)) (kv : α × Option Pub9 → Bound GQ → ℕ → GQ)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (K3.joinRun seat keys)) (ht : tmOf o = plainTm (jnVals hd lm jLK kv))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ a.1)) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true)
    (hkv : ∀ k, ((keysOf keys a.1).getD k (Aff.ofConst zeroE)).value Reading.gl
      (refWorld Reading.gl b.F [] (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))
        (dataQ own b (rdW w))) = kv (fixed9 φ a.1) (dataQ own b (rdW w)) k) :
    ItemIn L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  have hnamed := named_of_formsIn _ own o.1 o.2 a.1 b R hb hR hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt a.1 hsil R hR
  obtain ⟨F1, g, e1, e2⟩ := join_heard seat keys (l := z.1) (s' := z.2) hz
  obtain ⟨KF, -, -, hcl, hmk⟩ := joinRun_cut seat keys (cl := z.1) (s' := z.2) e1 e2 hz
  obtain rfl : G0 = F1 := Option.some.inj (hG0.symm.trans ((hA.fork a.1).symm.trans e1))
  obtain rfl : G0 = b.F := Option.some.inj (hG0.symm.trans (fork_of_atS hb))
  have hG' : G = b.F.paid g.owedJoin := by
    have h1 : (seat.mark a.1 (b.F.paid g.owedJoin)).fork? = some (b.F.paid g.owedJoin) := by
      rw [hA.mark]
      exact fork_putFork a.1 b.F hG0 _
    rw [hmk] at hG
    exact Option.some.inj (hG.symm.trans h1)
  have hlate : K9.lateOf b.F G = [] := by
    rw [hG']
    exact lateOf_same b.F _ rfl
  have hRz' : R = { forms := [Fo.joinForm g KF], late := [] } := by
    rw [hRz, hlate, hcl]
    show K9.Read.mk [(seat.claim (Fo.joinForm g KF)).form] [] = _
    rw [hA.form]
  subst hRz'
  have hq2 : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ a.1).1 = some g := by
    show hd (φ a.1) = _
    rw [← hφh]
    exact e2
  obtain ⟨su, okS, -⟩ := hk g (pubOf b) hg' hq2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  obtain ⟨G2, f2, -, -, -, -, hv⟩ := join_worth seat (·.form) hs lm keys GQ Reading.gl g jLK rs0 F0
    b.F 0 a.1 z.2 z.1 e2 e1 hI hL okS su hz
  obtain rfl : G2 = b.F.paid g.owedJoin := by
    rw [hmk, hs.markFork a.1 b.F _ e1] at f2
    exact (Option.some.inj f2).symm
  have hv' := hv _ (Fo.Later.refl _) (Fo.muOf (dataQ own b (rdW w)).mask)
    (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))
  rw [hcl] at hv'
  have hw : (b.F.paid g.owedJoin).worldOf Reading.gl
      (fun j => Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
      (entUnit (fixed9 φ a.1) (dataQ own b (rdW w))) =
      refWorld Reading.gl b.F [] (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))
        (dataQ own b (rdW w)) := by
    rw [refWorld_nil]
    rfl
  rw [hw] at hv'
  have hval : (Fo.joinForm g KF).value Reading.gl
      (refWorld Reading.gl b.F [] (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))
        (dataQ own b (rdW w))) =
      Fo.claimJoin g.shape lm jLK rs0 (Fo.muOf (dataQ own b (rdW w)).mask)
        (kv (fixed9 φ a.1) (dataQ own b (rdW w))) := by
    have h0 := List.head_eq_of_cons_eq hv'
    beta_reduce at h0
    rw [hA.form] at h0
    rw [h0]
    congr 1
    funext k
    exact hkv k
  refine ⟨b, _, [(⟨(o.2, K3.joinRun seat keys), tmOf o, lenOf o⟩, jnVals hd lm jLK kv)], hb, ?_, hR,
    hin, fun f hf => ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some (K3.joinRun seat keys)
        from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · refine List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, ?_⟩
    show f.value Reading.gl (worldOwn b [] (dataQ own b (rdW w))) ∈
      jnVals hd lm jLK kv (fixed9 φ a.1) (dataQ own b (rdW w))
    have hne := hnamed f hf
    obtain rfl : f = Fo.joinForm g KF := List.mem_singleton.1 hf
    rw [← value_meets_still b (dataQ own b (rdW w)) (fixed9 φ a.1) hq2 _ hne, hval]
    unfold jnVals
    rw [hp]
    exact List.mem_singleton.2 rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.item_join

#print axioms VerifiableInference.Desc.LinkJoin.refWorld_nil
