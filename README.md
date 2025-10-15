# Simple Semantics

[**Documentation**](https://michaelgoodale.com/simple-semantics/simple_semantics/index.html)

This repository defines a simple language of thought which represents basic primitives that are likely to be used in the semantics of natural language.
It also includes a lambda calculus which operates over that language of thought to model semantic composition, such as in a Montague Grammar.

It is designed largely to be used with [my minimalist grammar parser crate](https://github.com/MichaelGoodale/minimalist-grammar-parser)

## The lambda calculus

The lambda calculus is typed, with three atomic types and a functional type.
The three types are:

- Actors: Entities which receive theta roles
- Events: Entities which assign theta roles
- Truth Values: Standard bivalent truth values.

## The language of thought

The core language of thought is a first order logic with restricted quantification which has special primitives to govern theta role assignment.
