#!/bin/bash
coqc QandA.v
ocamlbuild QandA.native -use-ocamlfind -package io-system
