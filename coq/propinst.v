Require Import typesystem.
Require Import typesystemextra.

(** Type of propositional instances *)
Definition propinst (k : obj) :=
  (* [κ] := ∀(β:★). (Π(α:κ)β) → β *)
  TFor KStar (TArr (TPi (lift 1 0 k) (TVar (S O))) (TVar O)).

Lemma propinst_cobj :
  forall k, cobj k CKind -> cobj (propinst k) CType.
Proof.
  intros k Hk. repeat constructor.
  apply cobj_lift. auto.
Qed.

Lemma propinst_jeq :
  forall k k', jeq k k' CKind -> jeq (propinst k) (propinst k') CType.
Proof.
  intros k k' Hkk'. unfold propinst.
  do 5 constructor; auto.
  apply jeq_lift. auto.
Qed.

Lemma propinst_jobj :
  forall v H k,
    jobj v HNil (Jwf H CTEnv) ->
    jobj v H (JK k) ->
    jobj v H (JT (propinst k) KStar).
Proof.
  intros v H k HH Hk.
  destruct (jobj_class Hk) as [Hcobj Hclassjudg]. 
  simpl in Hclassjudg.
  unfold propinst.
  (* TFor *)
  constructor; [ constructor; auto | ].
  (* TArr *)
  constructor.
  (* TPi *)
  constructor.
  {
    intro Hmode.
    assert (jobj v H (Jwf k CKind)) as Hkwf
      by apply (jobj_extra Hmode Hk HH).
    replace (Jwf (lift 1 0 k) CKind)
    with (jlift 1 0 (Jwf k CKind))
      by auto.
    apply jobj_shift_0. auto. constructor.
  }
  {
    replace KStar with (lift 2 0 KStar) by auto.
    apply JTVar; repeat constructor. auto.
    apply cobj_lift. auto.
  }
  (* TVar *)
  replace KStar with (lift 1 0 KStar) by auto.
  apply JTVar; repeat constructor. auto.
Qed.


(* Term-level introduction and elemination forms *)
Require Import Llanguage.
Require Import Ltypesystem.

Definition deltaG_intro := Lam (Inst (Var 0)).
Definition deltaG_elim t u := App t (Gen u).

Lemma termgen_admissible :
  forall v H G k a t,
    jobj v H (JK k) ->
    jobj v (HCons H k) (JT t KStar) ->
    jterm v (HCons H k) (typesystem.lift 1 0 G) a t ->
    jterm v H G a (TFor k t).
Proof.
  intros v H G k a t Hk Ht Hat.
  destruct (jobj_class Hk) as [Hkcobj _].
  destruct (jobj_class Ht) as [_ [Htcobj _]].
  { apply (JCoer v H (HCons HNil k) (HCons H k) _ _ t); try intro Hmode.
    - repeat constructor.
    - apply (JHCons _ _ _ H).
      constructor.
      repeat (try constructor; assumption).
      assumption.
    - apply Ht.
    - assumption. 
    - { apply JCGen.
        - constructor. 
        - constructor.
        - assumption.
        - assumption.
        - intro. assumption.
      }
    }
Qed.  

Definition terminst_admissible :
  forall v H G k a t s,
    jobj v H (JK k) ->
    (mxx.mE v -> jobj v H (Jwf k CKind)) ->
    jterm v H G a (TFor k t) ->
    jobj v (HCons H k) (JT t KStar) ->
    jobj v H (JT s k) ->
    jterm v H G a (typesystem.subst s 0 t).
Proof.
  intros v H G k a t s Hk Hkwf Ha Ht Hs.
  destruct (jobj_class Hk) as [Hkcobj _].
  destruct (jobj_class Ht) as [_ [Htcobj _]].
  destruct (jobj_class Hs) as [_ [Hscobj _]].
  { apply (JCoer v H HNil H G a (TFor k t) (typesystem.subst s 0 t));
      try intro Hmode.
    - repeat constructor.
    - repeat constructor. assumption.
    - repeat constructor.
      assumption. assumption.
    - rewrite typesystem.lift_0. assumption.
    - apply JCInst; try intro Hmode;
        try repeat constructor; try assumption.
  }
Qed.

Lemma star_coherent :
  forall v H, cobj H CTEnv -> jobj v H (JK KStar).
Proof.
  intros v H.
  constructor.
  apply JPExi with (t := TOne); repeat constructor.
  assumption.
  intro Hmode.
  constructor.
  assumption.
Qed.  

Lemma deltaG_intro_jterm :
  forall v H G k s,
    cobj G CAEnv ->
    jobj v HNil (Jwf H CTEnv) ->
    jobj v HNil (JH H) ->
    jobj v H (JT s k) ->
    jterm v H G deltaG_intro (propinst k).
Proof.
  intros v H G k s HG Hhwf HH Hsk.
  destruct (jobj_class Hsk) as [Hkcobj _].
  assert (jobj v H (JK k)) as HJk. {
    constructor.
    apply JPExi with (t := s); try repeat constructor.
    assumption.
    intro Hmode.
    pose (jobj_extra Hmode Hsk Hhwf). simpl in e.
    assumption.
  }   
  destruct (jobj_class HJk) as [Hcobj Hclassjudg]. simpl in Hclassjudg.
  assert (mxx.mE v -> jobj v H (Jwf k CKind)) as Hkwf. {
    intro Hmode.
    apply (@jobj_extra v H _ Hmode HJk Hhwf).
  }
  unfold deltaG_intro. unfold propinst.
  { apply termgen_admissible.
    - apply star_coherent; assumption.
    - { repeat constructor.
        - intro Hmode.
          replace (Jwf (typesystem.lift 1 0 k) CKind)
          with (jlift 1 0 (Jwf k CKind)) by auto.
          apply (@jobj_shift_0 H KStar v). {
             apply Hkwf. assumption.
          }
          constructor.
        - replace KStar with (typesystem.lift 2 0 KStar) by auto.
          apply JTVar; repeat constructor. auto.
          apply cobj_lift. auto.
        -  replace KStar with (typesystem.lift 1 0 KStar) by auto.
           apply JTVar; repeat constructor. auto.
      }
    - { apply JLam.
        - intro Hmode.
          replace KStar with (typesystem.lift 1 0 KStar) by auto.
          apply JTVar; repeat constructor. auto.
        - { constructor.
            - intro Hmode.
              replace (Jwf (typesystem.lift 1 0 k) CKind)
              with (jlift 1 0 (Jwf k CKind))
                by auto.
              apply jobj_shift_0. auto. constructor.
            - replace KStar with (typesystem.lift 2 0 KStar) by auto.
              apply JTVar; repeat constructor. auto.
              apply cobj_lift. auto.
          }
        - { replace (TVar 0) with (typesystem.subst (typesystem.lift 1 0 s) 0 (TVar 1))
              by auto.
            { apply JInst with (k':= typesystem.lift 1 0 k).
              - intro Hmode.
                replace KStar with (typesystem.lift 2 0 KStar) by auto.
                apply JTVar; repeat constructor. auto.
                apply cobj_lift. auto.
              - { apply JVar.
                  - repeat constructor.
                    apply cobj_lift. assumption.
                    apply cobj_lift. assumption.
                  - intro Hmode.
                    constructor.
                    {
                      intro Hmode'.
                      replace (Jwf (typesystem.lift 1 0 k) CKind)
                      with (jlift 1 0 (Jwf k CKind))
                        by auto.
                      apply jobj_shift_0. auto. constructor.
                    }
                    {
                      replace KStar with (typesystem.lift 2 0 KStar) by auto.
                      apply JTVar; repeat constructor. auto.
                      apply cobj_lift. auto.
                    }
                  - repeat constructor.
                }
              - replace (JT (typesystem.lift 1 0 s) (typesystem.lift 1 0 k))
                with (jlift 1 0 (JT s k))
                  by auto.
                apply jobj_shift_0. auto. constructor.
            }
          } 
      }
  }
Qed.
  
  