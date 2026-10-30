-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3HostLaw.lean: the kind «lookup» (K3) as a HOST: the row on its guests, stated of the
true object behind a guest's form. Definitions, statements of type Prop that are not proved, and
small theorems that instantiate the library's theorem on the lookup with riders.

What it is for. Other kinds test identities of their own at coordinates of the point that the
lookup's key side draws. What the verifier computes for such a guest is a FORM: a linear form in
values (the reads) that come from an oracle message which is sent BEHIND that point. So «what the
guest reads is fixed before the draw» is false of the form. What is fixed in time is the IDENTITY
behind the form: an array on a cube whose entries are functions of the committed cells, claimed to
be 0 at every vertex; at a point z it is worth Σ_t eq(z, t) · g_t(cells): the array's multilinear
extension. The library's theorem on the lookup with riders (lookupCR_good,
Johnson/Top/H/LookupCRide.lean) is a statement on just that object. This file says what lies between
a guest as the text that runs has it (Guest, Johnson/Desc/First/Look/LookKind.lean) and a rider of
that theorem.

OBJECT: no text that runs: the library's lookup block with riders (kLookupCR,
  Johnson/Top/H/LookupCRide.lean).
USER: Johnson/Top/H/K3RiderTail.lean.
LETTERS: the caller c, the identities Gs, the forms, the map num and the list before: all free.
Compiled with the whole library.

Main names:
  `GuestId c`: a guest's identity at a caller c of the lookup: the places of the key point that it
    borrows; the oracle messages that it reads, as names of the caller's signature; the array.
  `GuestId.val`: the identity at a point. `GuestId.degLE`: it has degree at most 1 in each place
    (the library's degLE_ext_comp).
  `GuestId.ReadsOnly`: DEBT, the guest's kind's: the array hangs on the named messages alone.
  `GuestId.SentBefore`: the named messages are among the host's list `before`.
  `GuestForm`, `GuestForm.IsIdentity`: DEBT, the guest's kind's: the form at the TRUE reads is
    worth the identity at the point. That the SENT reads are the true ones is the premise h2 of
    `tgt_of_forms`: DEBT of the kind that closes the read equations.
  `riderOf c Gs`: the library's caller with riders that is made of a list of identities.
  `riderOf_src_congr`, `riderOf_tgt_congr`: under ReadsOnly the riders' source and target are the
    same at two tuples that agree at the named messages: so once these are bound both clauses are
    bound, whatever is laid later at the other names. What a composition can take from that debt.
  `tgt_of_forms`: PROVED: the forms' claims, with the two debts, give the riders' target.
  `hostPrice_in`: PROVED: the last key level's stretch of that list: 1, then 2 at each of its v - 1
    sumcheck rounds, then 2, 0, and 1 at the round LINE.
  `RiderBites`: DEBT: the use is not an empty one (Cb.Rider.forB_hollow).
  `isIdentity_zero`, `readsOnly_nil`: two debts tried against silly members.

IN TWO FILES. What ties a guest AS THE TEXT THAT RUNS HAS IT to an identity (Tells,
fits_parts, fits_lawful, k03_hosts, k03_hosts_one, HostAsks) stands over a version of
LookKind.lean in which a guest names its reads and the test caps its
degrees, which this library does not hold: that share RESTS, outside the library.
All that stands here imports no text that runs.

THE ERROR, AS NUMBERS. A rider adds nothing to any round's count: the list is the plain lookup's
(Cb.Fo's forB_eps). Taken by itself a false rider is rescued by at most 1 value of the
challenge in each of the v rounds that draw a place of the key point, and by none in any other round
(Cb.Rider.Carries.le at forB_carries, OnBytes/Tie/Pv/Lookup/Rider/ForB.lean; Blocks.doomed_rider).
The count of a round is the LARGER of the lookup's own and the rider's, not their sum
(Cb.Rider.know_both), for any number of riders, because to leave the state «some live equation is
false» a challenge must rescue every false one, so also one that was chosen before the draw.

THREE CAUTIONS THAT RIDE WITH THE ROW. (0) AT WHICH WITNESS THE MAXIMUM IS TAKEN: at a fixed tuple
m, for clauses that read the statement and m alone. For a clause that reads the further witness, or
what an extractor makes, the rule is FALSE: the counts add (know_not_both, further_not_know,
Cb/G6/Rider/PscTest.lean [not in this library]). A GuestId's array cannot read either, by type.
(1) The maximum is over riders that rescue DIFFERENT false
equations at ONE bound tuple of messages. The library's statement is for each fixed tuple m
(KnowAt): candidates for the tuple multiply, and are paid where the tuple is bound, at no rider.
(2) An equation that reads a tuple which does not exist must count as false. Here it does by form:
source and target are conjuncts of the joints' relations at a witness (m, wp) (withRider,
Cb/G6/Rider/Both.lean): where no m meets the joint behind the block, that joint is false.

Limits. c, its joint R0, the arrays and the map `num` from the signature's names to the plan's
numbers are free letters: no caller is given whose data are a sub-proof's own. ReadsOnly,
IsIdentity, the truth of the sent reads and RiderBites are shown of no guest here. THE
LIBRARY's STATEMENT SPEAKS FOR EACH FIXED TUPLE OF MESSAGES: for an array that reads a message which
is sent behind the lookup's first challenge it is true and of no worth (ForB.lean's own Limits):
ReadsOnly with SentBefore is what excludes that, AND NO THEOREM HERE USES THE TWO TOGETHER: the
order of sending is not a notion of the block's statement; it is one of whoever composes the blocks
(riderOf_src_congr and riderOf_tgt_congr are ReadsOnly's half, made ready for that hand).
Where the caller's signature holds just what has been sent up to the lookup (sentCaller,
Johnson/Top/H/LookupSeamsSent.lean) the type excludes it already. That `before` is sent in time is
the plan's test (FileDescription.beforeOk, Johnson/Desc/Block.lean), to the grain of a tree. That a later
block takes the target up, and anything on an honest prover, is not said.
NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.
Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Top.H.LookupCRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole
open Cb.Fo Cb.Rider

/-! ### lists -/

theorem getD_mem_of_lt {l : List ℕ} {t : ℕ} (ht : t < l.length) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  exact List.getElem_mem ht

theorem getD_inj_of_nodup {l : List ℕ} (hn : l.Nodup) :
    ∀ t < l.length, ∀ t' < l.length, l.getD t 0 = l.getD t' 0 → t = t' := by
  intro t ht t' ht' e
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    List.getElem?_eq_getElem ht', Option.getD_some, Option.getD_some] at e
  exact (List.Nodup.getElem_inj_iff hn).1 e

/-! ### the identity: the true object -/

/-- **A guest's identity at a caller of the lookup.** Data alone. -/
structure GuestId (c : LookupCCaller) : Type where
  /-- the places of the key point that it borrows, in the order of the cube's variables, the top bit
  first; place 0 of the key point belongs to the top bit of a key's number -/
  places : List ℕ
  /-- the oracle messages that it reads: names of the caller's signature. Public data -/
  reads : List c.Sg.O
  /-- the array: entry X, a function of the caller's state in front of the lookup and of the
  committed messages. By type it reads no challenge of the lookup and nothing of its transcript -/
  cells : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E

namespace GuestId
variable {c : LookupCCaller}

/-- **The identity at a point z of the key side**: Σ_X eq(z at the borrowed places, X) · cells X. -/
noncomputable def val (G : GuestId c) (st : c.St₀) (m : c.Sg.Msg) (z : ℕ → Cb.Gl.E) : Cb.Gl.E :=
  Blocks.ext G.places.length (G.cells st m) fun t => z (G.places.getD t 0)

/-- The places are different, and are places of the key point. -/
def Lawful (G : GuestId c) : Prop := G.places.Nodup ∧ ∀ j ∈ G.places, j ≤ FoNums.v' c.h

/-- **The identity has degree at most 1 in each place.** The library's degLE_ext_comp
(Blocks/StageBoth.lean). -/
theorem degLE (G : GuestId c) (hn : G.places.Nodup) (st : c.St₀) (m : c.Sg.Msg) :
    Alg.DegLE (fun _ => 1) (G.val st m) :=
  Blocks.degLE_ext_comp G.places.length (G.cells st m) (fun t => G.places.getD t 0)
    (getD_inj_of_nodup hn)

/-- **DEBT (the guest's kind): the array hangs on the named messages alone.** NOT PROVED of any
guest. (Where this and lean/THEOREM.md differ, the
page holds.) -/
def ReadsOnly (G : GuestId c) : Prop :=
  ∀ (st : c.St₀) (m m' : c.Sg.Msg), (∀ a ∈ G.reads, m a = m' a) → G.cells st m = G.cells st m'

/-- Under that debt the identity is fixed, as a function of the point, once the named messages are.
-/
theorem val_congr (G : GuestId c) (h : G.ReadsOnly) (st : c.St₀) {m m' : c.Sg.Msg}
    (e : ∀ a ∈ G.reads, m a = m' a) : G.val st m = G.val st m' := by
  funext z
  show Blocks.ext _ (G.cells st m) _ = Blocks.ext _ (G.cells st m') _
  rw [h st m m' e]

/-- **The named messages are among the host's list.** num: the number that the plan gives a name of
the signature: (chain, number in the chain's order of sending), as a block's `before` has it. -/
def SentBefore (G : GuestId c) (num : c.Sg.O → ℕ × ℕ) (before : List (ℕ × ℕ)) : Prop :=
  ∀ a ∈ G.reads, num a ∈ before

end GuestId

/-! ### the form: what the verifier computes -/

/-- **A guest's form, over letters.** -/
structure GuestForm (c : LookupCCaller) : Type 1 where
  /-- what the message of reads holds for this guest -/
  Rd : Type
  /-- what the typed form is worth: at the state, at values for the reads, at the key point -/
  worth : c.St₀ → Rd → (ℕ → Cb.Gl.E) → Cb.Gl.E
  /-- the TRUE reads at a point: made of the committed messages -/
  trueReads : c.St₀ → c.Sg.Msg → (ℕ → Cb.Gl.E) → Rd

/-- **DEBT (the guest's kind): the typed form at the true reads is worth the identity at the
point.** Algebra: no challenge is judged. NOT PROVED of any guest here. -/
def GuestForm.IsIdentity {c : LookupCCaller} (F : GuestForm c) (G : GuestId c) : Prop :=
  ∀ (st : c.St₀) (m : c.Sg.Msg) (z : ℕ → Cb.Gl.E), F.worth st (F.trueReads st m z) z = G.val st m z

/-! ### the rider that is made of the identities -/

/-- The library's caller with riders: one member for each identity of the list. -/
@[reducible] def riderOf (c : LookupCCaller) (Gs : List (GuestId c)) : LookupCRCaller where
  c := c
  ι := Fin Gs.length
  g := fun i => (Gs.get i).places.length
  sel := fun i t => (Gs.get i).places.getD t 0
  f := fun i => (Gs.get i).cells

/-- Lawful identities are a lawful choice: what lookupCR_good asks. -/
theorem riderOf_sel {c : LookupCCaller} {Gs : List (GuestId c)} (h : ∀ G ∈ Gs, G.Lawful) :
    SelLookupCR [riderOf c Gs] := by
  intro r hr
  obtain rfl : r = riderOf c Gs := List.mem_singleton.1 hr
  exact fun i => ⟨getD_inj_of_nodup (h _ (List.get_mem Gs i)).1,
    fun t ht => (h _ (List.get_mem Gs i)).2 _ (getD_mem_of_lt ht)⟩

theorem riderOf_ok {c : LookupCCaller} (Gs : List (GuestId c)) (hc : FoNums.ok c.h = true) :
    OkLookupC (callersCR [riderOf c Gs]) := by
  intro c' hc'
  obtain rfl : c' = c := List.mem_singleton.1 hc'
  exact hc

/-- The source: every identity's array is 0 on its cube. -/
theorem riderOf_src {c : LookupCCaller} (Gs : List (GuestId c)) (m : c.Sg.Msg)
    (a : c.St₀ × c.Ex.Str) :
    (riderOf c Gs).src m a ↔
      ∀ i : Fin Gs.length, ∀ X < 2 ^ (Gs.get i).places.length, (Gs.get i).cells a.1 m X = 0 :=
  Iff.rfl

/-- The target: every identity is 0 at the point of the claim on the keys. -/
theorem riderOf_tgt {c : LookupCCaller} (Gs : List (GuestId c)) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (riderOf c Gs).tgt m b ↔ ∀ i : Fin Gs.length, (Gs.get i).val b.1.1.1 m b.1.2.1.pt = 0 :=
  Iff.rfl

/-- Under ReadsOnly the riders' source hangs on the named messages alone. -/
theorem riderOf_src_congr {c : LookupCCaller} {Gs : List (GuestId c)}
    (hR : ∀ G ∈ Gs, G.ReadsOnly) {m m' : c.Sg.Msg}
    (e : ∀ G ∈ Gs, ∀ a ∈ G.reads, m a = m' a) (a : c.St₀ × c.Ex.Str) :
    (riderOf c Gs).src m a ↔ (riderOf c Gs).src m' a := by
  rw [riderOf_src, riderOf_src]
  refine forall_congr' fun i => ?_
  rw [hR _ (List.get_mem Gs i) a.1 m m' (e _ (List.get_mem Gs i))]

/-- Under ReadsOnly the riders' target hangs on the named messages alone. -/
theorem riderOf_tgt_congr {c : LookupCCaller} {Gs : List (GuestId c)}
    (hR : ∀ G ∈ Gs, G.ReadsOnly) {m m' : c.Sg.Msg}
    (e : ∀ G ∈ Gs, ∀ a ∈ G.reads, m a = m' a)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (riderOf c Gs).tgt m b ↔ (riderOf c Gs).tgt m' b := by
  rw [riderOf_tgt, riderOf_tgt]
  refine forall_congr' fun i => ?_
  rw [(Gs.get i).val_congr (hR _ (List.get_mem Gs i)) b.1.1.1 (e _ (List.get_mem Gs i))]

/-- **From the forms' claims to the riders' target.** h1: the first debt. h2: THE SECOND DEBT (the
kind that closes the read equations): the sent reads are the true ones at the point. h3: what the
link's batching is meant to give: each form, at the sent reads, is worth 0. -/
theorem tgt_of_forms {c : LookupCCaller} (Gs : List (GuestId c))
    (F : Fin Gs.length → GuestForm c) (h1 : ∀ i, (F i).IsIdentity (Gs.get i)) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) (sent : ∀ i, (F i).Rd)
    (h2 : ∀ i, sent i = (F i).trueReads b.1.1.1 m b.1.2.1.pt)
    (h3 : ∀ i, (F i).worth b.1.1.1 (sent i) b.1.2.1.pt = 0) : (riderOf c Gs).tgt m b :=
  (riderOf_tgt Gs m b).2 fun i => by
    have h := h3 i
    have e := h1 i b.1.1.1 m b.1.2.1.pt
    rw [h2 i, e] at h
    exact h

/-- **DEBT (the guest's kind with the host's): the use is not an empty one.** Some statement with
the condition `on` meets the joint before the block WITHOUT the riders while the riders' source
fails. Where this is false the statement with riders follows from the plain lookup's and says
nothing of the choice of places (Cb.Rider.forB_hollow). NOT PROVED of any caller. -/
def RiderBites (r : LookupCRCaller) : Prop :=
  ¬ ∀ (a : r.c.St₀ × r.c.Ex.Str) (w : r.c.Sg.Msg × r.c.Wp),
    (forIn Cb.Gl.E r.c.h r.c.L r.c.R0 r.c.msg₀).on a →
      (forIn Cb.Gl.E r.c.h r.c.L r.c.R0 r.c.msg₀).relR a w → r.src w.1 a


/-! ### the host's price, as numbers -/

/-- **The last key level's stretch of the lookup's list of bad challenges**: 1 (the sumcheck's
batching draw), 2 at each of its v' = v - 1 rounds, 2 (the further variable; drawn from the field
without 0), 0 (the end values), 1 (the round LINE). The v places of the key point are drawn in the
v' rounds and in LINE (Cb.Rider.forBB_vars, forB_carries). q: the field's size. -/
theorem hostPrice_in (q : ℕ) (h : Sh) :
    (TwErr.pscC (FoNums.v' h) 2 2 ++ [1]) <:+: forEps q h := by
  refine ⟨TwRound.shHead (FoNums.several h) (2 ^ h.d) ++
      ([2 ^ (FoNums.v' h + 1) - 1] ++
        (List.range (FoNums.n + 1)).flatMap (fun _ => TwErr.pscC 0 0 3) ++
        [FoNums.w * q ^ (FoNums.w - 1)] ++
        (List.range (FoNums.v' h)).flatMap fun l => TwErr.pscC l 2 2 ++ [1]),
    (List.range h.d).flatMap (fun l => TwErr.pscC (FoNums.w + l) 2 2 ++ [1]) ++
      ([1] ++ List.replicate h.d 2 ++ List.replicate FoNums.w 1) ++
      [(FoNums.w + h.d) * q ^ (FoNums.w + h.d - 1)] ++ TwErr.pscC (FoNums.w + h.d) 2 2, ?_⟩
  unfold forEps TwErr.epsN
  rw [List.range_succ (n := FoNums.v' h), List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-! ### the row against silly members -/

section Silly
variable {S Cl : Type}

/-- THE FORM THAT IS WORTH 0 EVERYWHERE (a verifier's test that says yes to all) meets the first
debt only where the identity's array is 0 on its cube at every state and every tuple: where the
identity is true of everything. By the library's vanishes_ext (Blocks/StageBoth.lean). -/
theorem isIdentity_zero {c : LookupCCaller} {G : GuestId c} (hn : G.places.Nodup)
    (F : GuestForm c) (hz : ∀ st r z, F.worth st r z = 0) (h : F.IsIdentity G) (st : c.St₀)
    (m : c.Sg.Msg) : ∀ X < 2 ^ G.places.length, G.cells st m X = 0 :=
  Blocks.vanishes_ext (g := G.places.length) (v := G.cells st m)
    (σ := fun t => G.places.getD t 0) (getD_inj_of_nodup hn)
    (z := fun _ => 0) (T := G.places) (fun _ ht => getD_mem_of_lt ht)
    fun z' _ => (h st m z').symm.trans (hz _ _ _)

/-- A GUEST THAT NAMES NO MESSAGE meets ReadsOnly only where the array reads no message at all. (The
text's test refuses such a guest.) -/
theorem readsOnly_nil {c : LookupCCaller} {G : GuestId c} (e : G.reads = []) (h : G.ReadsOnly)
    (st : c.St₀) (m m' : c.Sg.Msg) : G.cells st m = G.cells st m' :=
  h st m m' fun a ha => by rw [e] at ha; exact absurd ha List.not_mem_nil

end Silly

#print axioms VerifiableInference.OnPublicFiles.GuestId.degLE
#print axioms VerifiableInference.OnPublicFiles.GuestId.val_congr
#print axioms VerifiableInference.OnPublicFiles.riderOf_sel
#print axioms VerifiableInference.OnPublicFiles.riderOf_src_congr
#print axioms VerifiableInference.OnPublicFiles.riderOf_tgt_congr
#print axioms VerifiableInference.OnPublicFiles.tgt_of_forms
#print axioms VerifiableInference.OnPublicFiles.hostPrice_in
#print axioms VerifiableInference.OnPublicFiles.isIdentity_zero
#print axioms VerifiableInference.OnPublicFiles.readsOnly_nil

end VerifiableInference.OnPublicFiles
