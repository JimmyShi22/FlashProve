-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsShare.lean: THE KIND K1's SHARE OF THE THREADS' ExchangeS
AT THE ITEMS "forms m piece run", AT A SEGMENT's READS: from the item formsT in front and the item
"tie m" behind. Six definitions of premises' forms, one statement and its proof, over
Johnson/Desc/ProofFile/Honest/K1/Law/FormsFwd.lean and the threads' files
(Johnson/Desc/ProofFile/Honest/Thread/SharesS.lean,
Johnson/Desc/ProofFile/Honest/Thread/First.lean).

  FormsLetters       a record of the library's own letters of its two sentences on forms
  FormsAreLibrarys   equations on the threads' letters L: "forms" and "formsT" are the library's
                     sentences at these letters; the map of names and the mark "ahead" are the
                     table's own; and one field on the forms' letters alone: at every state St is
                     u's (stated: StatedIs, Johnson/Desc/Sound/StatedAll.lean)
  ReadsStepS         from the pair and the member's own step to the two states: public; no witness
  ArmBehindTieS      THE WEIGHT: behind the pair, the step AND THE TIE AT THAT WITNESS: the
                     committed cell is its stated function (ArmCellIn,
                     Johnson/Desc/Sound/StatedCellIn.lean)
  WtFwdS             "weights" goes forward: exchangeAtS_forms asks it at the output head's fifth
                     item alone (n = "weights"); ReadsSeated's field wt asks it bare, at the
                     record's own segment m, whichever that is
  ReadsSeated        the four in one record, with a field that ties the member's number b to the
                     segment m, AND WITH THREE EQUATIONS THAT TIE THE LETTERS OF THE FORMS
                     TO THE LETTERS AT WHICH THE KIND's PINS READ THE WITNESS: one list of codes,
                     one table of numbers, one list of members
  exchangeAtS_forms  THE SHARE. It takes its premises bare: it is built on no record

The lemmas of FormsFwd.lean bind the witness. exchangeAtS_forms lays them at the thread's own
witness, as the threads' form ExchangeAtS hands it. No equation on the Script is asked and no field
of it is read.

WHO HAS MET WHAT. FormsAreLibrarys: meant to hold by unfolding at the threads' letters over the
library's composed meaning (mgAll_forms, mgAll_formsT: Johnson/Desc/Sound/MgAll.lean); not stated
here. ReadsStepS: its parts lie as lemmas (laterSend_blkL, laterGrows_k1Reads, seats_new,
seats_in_group in the library; readers_later_all, found_later_all in
Johnson/Desc/ProofFile/Honest/K1/Law/PubBehindAtFifty.lean); not joined. ArmBehindTieS: NOBODY. The
library pays the same equation behind the tie, but every payer that takes its fence (ReadsFence,
Johnson/Desc/K1/Law/ArmAtReads.lean) takes the library's whole promise, which a thread has at its
own letters alone. WtFwdS: its law is wt_fwd_reads
(Johnson/Desc/ProofFile/Honest/K1/Law/WtFwdReads.lean); not joined. The share at "tie m": NOBODY.
ReadsSeated's three equations and its field place: nobody. The letter wt of FormsLetters:
FormsAreLibrarys holds it against the threads' own sentences forms and formsT at the run "weights",
and WtFwdS asks that it goes forward; no field says what it says.

Limits. NO MEMBER OF ANY OF THE SIX IS GIVEN. The six are definitions: nothing is claimed of them,
and no goal file names them. At an item that stands for no run (at a layers' segment
"planes" and "join") both sentences hold of every witness and the share says nothing. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsFwd
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart Item PubData segRow shift runsOf)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.Sound (MsgT Stated UFn StatedIs ArmCellIn seatTab)
open VerifiableInference.Desc.K1 (RecRides SecondFound ReadersStay)
open ProofFile.Honest.FirstThread (Letters)

/-- **The letters of the library's two sentences on forms.** Of D: cs, Rd, runs, N, ah. -/
structure FormsLetters (P Cells Tok : Type) where
  D : PubData
  ms : List Sound.Mem
  St : Stated
  u : UFn
  after : ℕ → S → Except String S
  wt : ℕ → P × S → Strs → Wit Cells Tok MsgT → Prop
  rwB : ℕ → S → Bool

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}

/-- **Equations on the threads' letters**, and one field on 𝔉 alone (stated). A definition: a
premise's form. -/
structure FormsAreLibrarys (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (𝔉 : FormsLetters P Cells Tok) (arr : ℕ → ℕ → ℕ) : Prop where
  forms : ∀ w, (L.Mg w).forms = (Sound.meaningForms 𝔉.D.cs arr 𝔉.ms 𝔉.D.Rd 𝔉.D.runs 𝔉.St 𝔉.after
    𝔉.D.N 𝔉.wt 𝔉.rwB 𝔉.D.ah (L.Mg w)).forms
  formsT : ∀ w, (L.Mg w).formsT = (Sound.meaningForms 𝔉.D.cs arr 𝔉.ms 𝔉.D.Rd 𝔉.D.runs 𝔉.St 𝔉.after
    𝔉.D.N 𝔉.wt 𝔉.rwB 𝔉.D.ah (L.Mg w)).formsT
  stated : ∀ s, StatedIs 𝔉.St 𝔉.u s
  runs : ∀ m k r, 𝔉.D.runs m k r = Sound.runsAt L.links m k r
  ah : ∀ k r, 𝔉.D.ah k r = (r == "K8.equations")

/-- **From the pair and the member's own step to the two states**: public; no witness in it. A
definition: a premise's form. -/
def ReadsStepS (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (𝔉 : FormsLetters P Cells Tok)
    (b m j : ℕ) (n : String) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∃ new, RecRides new s s' ∧ Grows s.st s'.st ∧ s.book.place.size = s.st.oracles.size ∧
      (∀ o ∈ new, (seatAt (𝔉.D.N.group m) s'.book o).isSome = true) ∧ SecondFound new s s' ∧
      ReadersStay 𝔉.D m j n s s'

/-- **THE WEIGHT**: behind the pair, the step AND THE TIE AT THAT WITNESS: the committed cell is its
stated function. v: any witness. It is handed the tables as sent, whole (Env.strs): more than the
positions that a verifier reads. This letter is for the honest run's own forms alone: no statement
on any other party may take it. A
definition: a premise's form. -/
def ArmBehindTieS (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (𝔉 : FormsLetters P Cells Tok)
    (arr : ℕ → ℕ → ℕ) (b m j : ℕ) (n : String) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ v, (L.Mg μ.st.input).tie m (L.pubOf μ.st.input.x, s') (L.thread.strs (E.add y.1)) v →
    ∀ p ∈ 𝔉.D.runs m j n, ∀ a c, segAt? s = some a → segAt? s' = some c →
      ArmCellIn (𝔉.D.Rd m) (𝔉.D.N.sent m 0) (𝔉.D.N.group m) p.1 p.2 s a c
        (seatTab 𝔉.D.cs arr 𝔉.ms v) 𝔉.u

/-- "weights" goes forward. exchangeAtS_forms asks it at the output head's fifth item alone;
ReadsSeated's field wt asks it bare, at the record's own segment m, whichever that is. It is handed
the tables as sent, whole (Env.strs): more than the positions that a verifier reads. This letter is
for the honest run's own forms alone: no statement on any other party may take it.
A definition: the form of a premise. -/
def WtFwdS (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (𝔉 : FormsLetters P Cells Tok)
    (b m : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ v, 𝔉.wt m (L.pubOf μ.st.input.x, s) (L.thread.strs E) v →
      𝔉.wt m (L.pubOf μ.st.input.x, s') (L.thread.strs (E.add y.1)) v

/-- **The share's premises in one record. NO FIELD SAYS WHAT 𝔉.wt SAYS**: formsM holds it against
the threads' own sentences forms and formsT at the run "weights", and the field wt asks that it goes
forward. At the member number b, the reads of segment m: place: THE FIELD THAT TIES b TO m. cs, ms:
the codes and the members at which the kind's pins read the witness: the letters of the kind's own
record of premises K1Seated (Johnson/Desc/ProofFile/Honest/K1/Seated.lean; there cs is J.P.codes).
THE THREE EQUATIONS TIE THE FORMS' READER OF THE WITNESS TO THE PINS'. A definition: a premise's
form. -/
structure ReadsSeated (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (𝔉 : FormsLetters P Cells Tok)
    (arr : ℕ → ℕ → ℕ) (cs : OnBytes.Codes) (ms : List Sound.Mem) (b m : ℕ) : Prop where
  place : ∃ sub, L.links[m]? = some sub ∧
    L.ps[b]? = some { chain := 1, link := some m, piece := 4 + shift sub, kind := .K1 }
  formsM : FormsAreLibrarys L 𝔉 arr
  codes : 𝔉.D.cs = cs
  numbers : 𝔉.D.N = L.N
  members : 𝔉.ms = ms
  step : ∀ j n, ReadsStepS L Said 𝔉 b m j n
  arm : ∀ j n, ArmBehindTieS L Said 𝔉 arr b m j n
  wt : WtFwdS L Said 𝔉 b m

/-- **THE SHARE**: ExchangeAtS at the item forms m j n, at the member number b: from the item
formsT m j n in front (hi), the share at the item tie m (hTie) and four premises' forms, taken
bare. sub, hsub, ho: the item is one that the table's row at segment m's reads owes. -/
theorem exchangeAtS_forms {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b m : ℕ}
    {𝔉 : FormsLetters P Cells Tok} {arr : ℕ → ℕ → ℕ} (hF : FormsAreLibrarys L 𝔉 arr)
    {sub : ModelPart} (hsub : L.links[m]? = some sub) {j : ℕ} {n : String}
    (ho : Item.forms m j n ∈ (segRow sub m (4 + shift sub)).outs)
    (hi : Item.formsT m j n ∈ L.thread.opened b)
    (hStep : ReadsStepS L Said 𝔉 b m j n) (hArm : ArmBehindTieS L Said 𝔉 arr b m j n)
    (hWt : n = "weights" → WtFwdS L Said 𝔉 b m)
    (hTie : ExchangeAtS L.thread Said b (.tie m)) :
    ExchangeAtS L.thread Said b (.forms m j n) := by
  intro blk hblk k s μ E ds y cols s' hA hd hS ds' i hi'
  obtain rfl := List.mem_singleton.1 hi'
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, hI0, -, -, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have h0 : (L.Mg μ.st.input).formsT m j n (L.pubOf μ.st.input.x, s) (L.thread.strs E)
      (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) := hI0 (ds ++ ds') (.formsT m j n) hi
  have ht : (L.Mg y.2.st.input).tie m (L.pubOf y.2.st.input.x, s') (L.thread.strs (E.add y.1))
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) :=
    hTie blk hblk k s μ E ds y cols s' hA hd hS ds' (.tie m) (List.mem_singleton.2 rfl)
  rw [ei, eh, List.append_assoc] at ht
  obtain ⟨new, hR, hg, hfull, hseat, hfound, hRd⟩ := hStep blk hblk k s μ E ds y cols s' hA hd hS
  have hah : ∀ p ∈ 𝔉.D.runs m j n, 𝔉.D.ah p.1 p.2 = false := by
    intro p hp
    rw [hF.runs] at hp
    unfold Sound.runsAt at hp
    rw [hsub] at hp
    rw [hF.ah]
    exact (reads_shuts sub m j n ho).2 p hp
  show (L.Mg y.2.st.input).forms m j n (L.pubOf y.2.st.input.x, s') (L.thread.strs (E.add y.1))
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc, hF.forms]
  rw [hF.formsT] at h0
  exact forms_of_formsT 𝔉.D arr 𝔉.ms 𝔉.St 𝔉.u 𝔉.after 𝔉.wt 𝔉.rwB (L.Mg μ.st.input)
    (L.pubOf μ.st.input.x, s) (L.pubOf μ.st.input.x, s') _ _ _ m j n (hF.stated s) hR hg hfull hah
    hRd hseat hfound (hArm blk hblk k s μ E ds y cols s' hA hd hS _ ht)
    (fun e => hWt e blk hblk k s μ E ds y cols s' hA hd hS _) h0

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.FormsLetters
#print axioms ProofFile.Honest.K1.FormsAreLibrarys
#print axioms ProofFile.Honest.K1.ReadsStepS
#print axioms ProofFile.Honest.K1.ArmBehindTieS
#print axioms ProofFile.Honest.K1.WtFwdS
#print axioms ProofFile.Honest.K1.ReadsSeated
#print axioms ProofFile.Honest.K1.exchangeAtS_forms
