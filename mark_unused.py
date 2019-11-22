#!/usr/bin/env python3

import os, re

unused_str = '(* unused *)'

def build_src(key,name):
    return key + ' ' + name + ' '

def build_target(key,name):
    return key + ' ' + name + ' ' + unused_str

# careful: for some reason too many definitions are marked unused 
def mark_unused_all(path):
#    os.system('coqc -R ./ UniAna dpd.v')
#    os.system('dpdusage graph.dpd > unused.dump')
    keyws = ['Lemma','Theorem','Definition','Inductive','Corollary','Parameter']
    for f_coq_path in os.listdir(path):
        if ~f_coq_path.startswith('.#') & f_coq_path.endswith('.v'):
            with open(path + '/' + f_coq_path,'r') as file_coq:
                coq_data = file_coq.read()
                coq_data = coq_data.replace(unused_str,"")
            with open('unused.dump','r') as file_u:
                for line in file_u:
                    splitting = re.split('\s|:',line)
                    lsplit = splitting[0]
                    rsplit = splitting[1]
                    if (f_coq_path.startswith(lsplit)):
                        print("replacing " + rsplit + " in " + lsplit)
                        for key in keyws:
                            coq_data = coq_data.replace(build_src(key,rsplit),build_target(key,rsplit))
            with open(path + '/' + f_coq_path,'w') as file_coq:
                file_coq.write(coq_data)
                print ("wrote " + f_coq_path)
                            

mark_unused_all(".")
mark_unused_all("tcfg")
mark_unused_all("infra")
mark_unused_all("cfg")
mark_unused_all("eval")
mark_unused_all("util")
mark_unused_all("disj")
                    
                    
    
    

