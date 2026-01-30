theory DDL_inference
  imports DDL_main
begin

 abbreviation body :: "rule \<Rightarrow> \<sigma> set" where "body r \<equiv> fst r"
 abbreviation head :: "rule \<Rightarrow> \<sigma>" where "head r \<equiv> snd r"

 abbreviation Opposite :: "rule \<Rightarrow> rule \<Rightarrow> bool" where "Opposite s r \<equiv> heads_opposite s r"
 abbreviation ReflexiveM :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> bool" where "ReflexiveM M \<equiv> (M = OB \<longrightarrow> reflexive N_OBL)"
 abbreviation is_lit   :: "\<sigma> \<Rightarrow> bool" where "is_lit x \<equiv> True"
 abbreviation is_posM  :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> \<sigma> \<Rightarrow> \<sigma> \<Rightarrow> bool" where "is_posM M x a \<equiv> (x = M a)"
 abbreviation is_negM  :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> \<sigma> \<Rightarrow> \<sigma> \<Rightarrow> bool" where "is_negM M x a \<equiv> (x = (\<lambda>w. \<not> (M a w)))"

 abbreviation no_defeat :: "rule \<Rightarrow> bool" where "no_defeat r \<equiv> True"
 abbreviation applicable :: "rule \<Rightarrow> bool" where "applicable r \<equiv> (body r \<subseteq> F) \<and> no_defeat r"

 (* Def. 4*)
 abbreviation conclusion :: "\<sigma> \<Rightarrow> bool" where
    "conclusion \<phi> \<equiv>  (\<phi> \<in> D_plus \<or> \<phi> \<in> D_minus \<or> \<phi> \<in> D_plus_OBL \<or> \<phi> \<in> D_minus_OBL)"
 
 abbreviation provable_fact ("p+ _" [100] 100) where "p+ \<phi> \<equiv> \<phi> \<in> D_plus"

 abbreviation refutable_fact ("p- _" [100] 100) where "p- \<phi> \<equiv> \<phi> \<in> D_minus"

 abbreviation provable_obl ("p+OBL _" [100] 100) where "p+OBL \<phi> \<equiv> \<phi> \<in> D_plus_OBL"

 abbreviation refutable_obl ("p-OBL _" [100] 100) where "p-OBL \<phi> \<equiv> \<phi> \<in> D_minus_OBL"

 (*Def. 5*)
 inductive
   d_pos :: "\<sigma> \<Rightarrow> bool"  ("+d _" [100] 100)
 and d_neg :: "\<sigma> \<Rightarrow> bool" ("-d _" [100] 100)
 and mpos  :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> rule set \<Rightarrow> \<sigma> \<Rightarrow> bool" ("+dM _ _ _" [100,100,100] 100)
 and mneg  :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> rule set \<Rightarrow> \<sigma> \<Rightarrow> bool" ("-dM _ _ _" [100,100,100] 100)
 where
   d_pos_fact:
     "\<phi> \<in> F \<Longrightarrow> +d \<phi>"

 | d_pos_from_obl:
     "ReflexiveM OB \<Longrightarrow> mpos OB R_OBL \<phi> \<Longrightarrow> +d \<phi>"

 | mpos_intro:
     "r \<in> R \<Longrightarrow> applicable r \<Longrightarrow> head r = M l \<Longrightarrow> l \<notin> F \<Longrightarrow> mpos M R l"

 | mneg_intro:
     "l \<notin> F \<Longrightarrow> (\<forall>r\<in>R. head r = M l \<longrightarrow> \<not> applicable r) \<Longrightarrow> mneg M R l"

 | d_neg_nonfact:
     "\<phi> \<notin> F \<Longrightarrow> (mneg OB R_OBL \<phi> \<or> \<not> reflexive N_OBL) \<Longrightarrow> -d \<phi>"

 abbreviation D_plus :: "\<sigma> set" where
  "D_plus \<equiv> {\<phi>. d_pos \<phi>}"

 abbreviation D_minus :: "\<sigma> set" where
  "D_minus \<equiv> {\<phi>. d_neg \<phi>}"

 (*Def 6*)
 type_synonym ext = "\<sigma> set \<times> \<sigma> set"

 abbreviation Ext_M :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> rule set \<Rightarrow> ext" where "Ext_M M R \<equiv> ({\<phi>. mpos M R \<phi>}, {\<phi>. mneg M R \<phi>})"

 abbreviation Ext_OBL :: ext where "Ext_OBL \<equiv> Ext_M OB R_OBL"

 lemma in_Ext_M_pos[simp]: "\<phi> \<in> fst (Ext_M M R) \<longleftrightarrow> mpos M R \<phi>"
   by simp

 lemma in_Ext_M_neg[simp]: "\<phi> \<in> snd (Ext_M M R) \<longleftrightarrow> mneg M R \<phi>"
   by simp

 (*Def. 13*)
abbreviation D_mod_plus :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> rule set \<Rightarrow> \<sigma> set" where
  "D_mod_plus M R \<equiv> {l. mpos M R l}"

abbreviation D_mod_minus :: "(\<sigma>\<Rightarrow>\<sigma>) \<Rightarrow> rule set \<Rightarrow> \<sigma> set" where
  "D_mod_minus M R \<equiv> {l. mneg M R l}"

abbreviation D_plus_OBL :: "\<sigma> set" where
  "D_plus_OBL \<equiv> { OB l | l. l \<in> D_mod_plus OB R_OBL }"

abbreviation D_minus_OBL :: "\<sigma> set" where
  "D_minus_OBL \<equiv> { \<^bold>\<not> (OB l) | l. l \<in> D_mod_minus OB R_OBL }"

abbreviation D_extension ("E") where
  "E \<equiv> D_plus \<union> D_minus \<union> D_plus_OBL \<union> D_minus_OBL"

end