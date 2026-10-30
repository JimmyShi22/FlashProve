-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorMaps.lean: the four items that the last chain takes over at its start, as congruences:
each holds at one witness and is read at another that agrees with it as each premise says; and the
row (Dot) at words that agree with the linear claim's.

Why. The last thread's first border asks five items at the witness of its own run. Four were laid
by an earlier chain at that chain's witness: the two pins and the row (Eval) of the first, Omega's
pin of the shared. The fifth, (Dot), is new.

Main names.
  `pin_map`: the honest pin of a message, at a witness that lays the same table there.
  `valOf_same`: the reading of the statement's messages, where the witnesses' tables agree.
  `srow_map`, `eval_map`: a message's sample rows and the row (Eval) of the first chain's
    meaning.
  `omega_map`: Omega's sample rows, at words that agree on its number, in a statement in order.
  `dot_words`: the row (Dot) says yes at any words and any number, where those words agree with
    the linear claim's at Omega's places: the tie `hTie`. In place of `dot_says_key`'s premise on
    Omega it asks `hTie` and three more (`hP`, `hl`, `hRw`). One of its premises is spare: `hpsi`
    follows from `hrow` (a step of `dot_terms_form`, E2E/KeyDotFits.lean, not imported here).

What stays open. THE LAST CHAIN's ROW (Dot) STANDS AT OMEGA's COPY, A NUMBER OF ITS OWN: the shared
chain's Omega is number 2, the row's is the first chain's count of messages. `hTie` is that
renumbering, and no file pays it. One lens, two numberings: `omega_map` reads the shared
statement's number, (Dot) and (Eval) the last chain's: which lens each reads, no file says.
`omega_map` gives one number at a call; Omega's pin asks every message with Omega's tenant, and the
numbers' table is a letter.
Each map is stated at letters: which witness the last thread reads, and how `Mg₀`'s `ev` and `dot`
are laid, no file says at a key. `valOf_same` asks the agreement at every number that `K.num`
answers: at the first chain's witnesses that needs `K.num` to answer below 3 alone, a test on the
plan that is owed. That the items' sentences at a thread are these meanings, through `KItem.holds`,
is not stated. The half on W of (Dot) is the premise `hW`. Nothing here joins the items to the
door's law, and that a thread holds them at a run is said nowhere here.

NOT IN FRONT OF A LAW OVER COINS: `dot_words` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: of the first kind `hRw` and `hTie`, which tie
the letter `H` and the words to the committer's pads and tails; of the second kind `hW`, `hmat`,
which read the hidden matrix. None: the bar is flat: no lemma here lays in the made terms, `holds2`
and the witness of a run. `hP` and `hl` name no coin. The maps and `valOf_same` name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyRest
import E2E.KeyDotSays
import E2E.KeyOmegaWords
import Johnson.Desc.K14.Honest.ItemsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyDoorMaps
open VerifiableInference.Desc (FileDescription Reading Strs Wit msgOf)
open VerifiableInference.Desc.Key (KItem KMeaning KPlan KRead KReaders Where valOf meaning₁
  RowHolds)
open AtPublicFiles.KeyThread (holdsH)

section pins
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)
  (at_ : Where) (meetsT : Rec → Cells → Prop) (Mg : KMeaning P S (Wit Cells Unit M))

/-- **The honest pin of message k**, at a witness that lays the same table at its seat. -/
theorem pin_map (k : Nat) (a : P × S) (y y' : Strs) (u u' : Wit Cells Unit M)
    (e : msgOf G u (at_ k).1 (at_ k).2 = msgOf G u' (at_ k).1 (at_ k).2)
    (h : holdsH F G at_ meetsT Mg (.pin k) a y u) :
    holdsH F G at_ meetsT Mg (.pin k) a y' u' := by
  obtain ⟨o, z, ho, hz, hm⟩ := h
  exact ⟨o, z, ho, hz, e ▸ hm⟩

end pins

section rows
variable {P S Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders S)

/-- The statement's messages read off two witnesses, where their tables agree. -/
theorem valOf_same (u u' : Wit Cells Unit M) (h : ∀ o k, K.num o = some k → R.of u k = R.of u' k) :
    valOf K R u = valOf K R u' := by
  funext o part i
  unfold valOf
  cases e : K.num o with
  | none => rfl
  | some k =>
    show R.val (R.of u k) part i = R.val (R.of u' k) part i
    rw [h o k e]

variable (near : Nat → P × S → Strs → Prop) (forms worth other : Nat → String → P × S → Strs →
  Wit Cells Unit M → Prop)

/-- **A message's sample rows**, at a witness that reads the same. -/
theorem srow_map (k : Nat) (a : P × S) (y y' : Strs) (u u' : Wit Cells Unit M)
    (hv : valOf K R u = valOf K R u')
    (h : (meaning₁ K R X near forms worth other).srow k a y u) :
    (meaning₁ K R X near forms worth other).srow k a y' u' := by
  obtain ⟨o, x, ho, hx, hs, hz, hr⟩ := h
  refine ⟨o, x, ho, hx, hs, hz, fun r hm => ?_⟩
  rw [← hv]
  exact hr r hm

/-- **The row (Eval)**, at a witness that reads the same. -/
theorem eval_map (a : P × S) (y y' : Strs) (u u' : Wit Cells Unit M)
    (hv : valOf K R u = valOf K R u')
    (h : (meaning₁ K R X near forms worth other).claim 1 "Eval" a y u) :
    (meaning₁ K R X near forms worth other).claim 1 "Eval" a y' u' := by
  have hc : (1 : Nat) = 1 ∧ "Eval" = "Eval" := ⟨rfl, rfl⟩
  unfold meaning₁ at h ⊢
  dsimp only at h ⊢
  rw [if_pos hc] at h ⊢
  obtain ⟨r, hr, hs⟩ := h
  refine ⟨r, hr, ?_⟩
  rw [← hv]
  exact hs

end rows

/-- **Omega's sample rows**, at words that agree on its number, in a statement in order. -/
theorem omega_map {s : _root_.Desc.K14.St} {m m' : OnBytes.Means.Words Cb.Gl.E}
    (hI : OnBytes.Means.InOrder s.st) (o : Nat)
    (e : ∀ part j, m o part j = m' o part j) (h : _root_.Desc.K14.Honest.SmpOwn o s m) :
    _root_.Desc.K14.Honest.SmpOwn o s m' := by
  obtain ⟨x, hx, hs⟩ := h
  refine ⟨x, hx, fun r hr => ?_⟩
  refine (OnBytes.Means.says_agree OnBytes.Slice.rdE (hI.samples o x hx r hr)
    (fun o' ho' part j => ?_)).1 (hs r hr)
  have e' : o' = o := by simpa using ho'
  rw [e']
  exact e part j

/-- **The row (Dot) says yes at words that hold the linear claim's Omega**: at any number in the
statement at which the row is laid, where those words agree with the linear claim's on the
layout's places below the matrix's rows.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem dot_words {P : _root_.Desc.K14.P14} {sentU : Array OnBytes.OracleNotice}
    {layO : OnBytes.TreeLay} (hP : _root_.Desc.K14.Honest.PlanFacts P.par P.codes sentU layO)
    (d0 : _root_.Desc.K14.St) (r1 : Fmt.RoundView) (H : _root_.Desc.K14.Honest.Inputs)
    {l : _root_.Desc.K14.Lin} (hl : _root_.Desc.K14.Honest.Notes P d0 r1 l)
    (T : OnBytes.Statement) (ws : List OnBytes.Tensor) (n : Nat) (lay : OnBytes.VectorLay)
    (w : Nat) (wLay : OnBytes.VectorLay) (row : OnBytes.Row)
    (hrow : OnBytes.linDotRow P.par.S ws l.psiSh n lay w wLay = some row)
    (hok : ∀ g ∈ ws, g.ok = true)
    (hPl : _root_.Desc.K14.Law.PlacedDot T P.par.S n lay w wLay)
    (entry pad tail : Nat → Nat → OnBytes.Slice.GF)
    (mat : Fin P.par.S.matrixRows → (Fin P.par.S.kCol → Bool) → OnBytes.Slice.GE)
    (hmat : ∀ (i : Fin P.par.S.matrixRows) (e : Nat), e < 2 ^ P.par.S.kCol →
      mat i (VerifiableInference.Desc.K13.Law.lowBits P.par.S.kCol e) =
        algebraMap OnBytes.Slice.GF OnBytes.Slice.GE (entry i.val e))
    (m : OnBytes.Means.Words OnBytes.Slice.GE)
    (hW : VerifiableInference.Desc.K13.Law.WIs mat m ws w wLay)
    (hTie : ∀ y < P.par.S.matrixRows, m n .main (lay.index y) =
      _root_.Desc.K14.Honest.omegaAt P d0 (_root_.Desc.K14.Honest.words2 P sentU d0 r1 H) y)
    (hRw : ∀ r j, H.Rw r j =
      OnBytes.Slice.rdE.val (ProofFile.Honest.K14.rowsOf P.par.S ⟨entry⟩ ⟨pad, tail⟩ r j))
    (hpsi : l.psiSh.length = P.par.S.kCol) :
    OnBytes.Means.Says VerifiableInference.Desc.K13.Law.ρg T row m :=
  have hg : (_root_.Desc.K14.gamma P.par.S l).length = P.par.S.fold.index.v := by
    have h : l.psiSh.length = P.par.S.kLo + P.par.S.fold.index.v := hpsi
    show (l.psiSh.drop P.par.S.kLo).length = _
    rw [List.length_drop, h]
    omega
  have hE : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.entries :=
    Nat.le_trans (AtPublicFiles.KeyOmegaWords.room_of_plan hP)
      (Nat.le_trans (_root_.Desc.K14.Honest.ell_le_tailFirst _)
      (Nat.le_add_right _ _))
  AtPublicFiles.Key.dot_says_key T P.par.S ws l.psiSh n lay w wLay row hrow hok hPl entry pad tail mat hmat
    m hW (fun y hy => (hTie y hy).trans
      (AtPublicFiles.KeyOmegaWords.hOm_words2 hP d0 r1 H hl _ hRw hg y hy)) hpsi rfl hE

end AtPublicFiles.KeyDoorMaps

#print axioms AtPublicFiles.KeyDoorMaps.pin_map
#print axioms AtPublicFiles.KeyDoorMaps.valOf_same
#print axioms AtPublicFiles.KeyDoorMaps.srow_map
#print axioms AtPublicFiles.KeyDoorMaps.eval_map
#print axioms AtPublicFiles.KeyDoorMaps.omega_map
#print axioms AtPublicFiles.KeyDoorMaps.dot_words
