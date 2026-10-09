ast_enum! {
    /// A binary operator: `+`, `+=`, `&`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum BinOp {
        /// The `+` operator (addition)
        Add(Token![+]),
        /// The `-` operator (subtraction)
        Sub(Token![-]),
        /// The `*` operator (multiplication)
        Mul(Token![*]),
        /// The `/` operator (division)
        Div(Token![/]),
        /// The `%` operator (modulus)
        Rem(Token![%]),
        /// The `&&` operator (logical and)
        And(Token![&&]),
        /// The `||` operator (logical or)
        Or(Token![||]),
        /// The `^` operator (bitwise xor)
        BitXor(Token![^]),
        /// The `&` operator (bitwise and)
        BitAnd(Token![&]),
        /// The `|` operator (bitwise or)
        BitOr(Token![|]),
        /// The `<<` operator (shift left)
        Shl(Token![<<]),
        /// The `>>` operator (shift right)
        Shr(Token![>>]),
        /// The `==` operator (equality)
        Eq(Token![==]),
        /// The `<` operator (less than)
        Lt(Token![<]),
        /// The `<=` operator (less than or equal to)
        Le(Token![<=]),
        /// The `!=` operator (not equal to)
        Ne(Token![!=]),
        /// The `>=` operator (greater than or equal to)
        Ge(Token![>=]),
        /// The `>` operator (greater than)
        Gt(Token![>]),
        /// The `+=` operator
        AddAssign(Token![+=]),
        /// The `-=` operator
        SubAssign(Token![-=]),
        /// The `*=` operator
        MulAssign(Token![*=]),
        /// The `/=` operator
        DivAssign(Token![/=]),
        /// The `%=` operator
        RemAssign(Token![%=]),
        /// The `^=` operator
        BitXorAssign(Token![^=]),
        /// The `&=` operator
        BitAndAssign(Token![&=]),
        /// The `|=` operator
        BitOrAssign(Token![|=]),
        /// The `<<=` operator
        ShlAssign(Token![<<=]),
        /// The `>>=` operator
        ShrAssign(Token![>>=]),

        // verus
        Equiv(Token![<==>]),
        Imply(Token![==>]),
        Exply(Token![<==]),
        BigEq(Token![===]),
        BigNe(Token![!==]),
        ExtEq(Token![=~=]),
        ExtNe(Token![!~=]),
        ExtDeepEq(Token![=~~=]),
        ExtDeepNe(Token![!~~=]),
    }
}

ast_enum! {
    /// A unary operator: `*`, `!`, `-`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum UnOp {
        /// The `*` operator for dereferencing
        Deref(Token![*]),
        /// The `!` operator for logical inversion
        Not(Token![!]),
        /// The `-` operator for negation
        Neg(Token![-]),

        // verus
        Proof(Token![proof]),
        Forall(Token![forall]),
        Exists(Token![exists]),
        Choose(Token![choose]),
    }
}

#[cfg(feature = "parsing")]
pub(crate) mod parsing {
    use crate::buffer::Cursor;
    use crate::error::Result;
    use crate::op::{BinOp, UnOp};
    use crate::parse::{Parse, ParseStream};

    /// Returns whether the current token can begin a binary operator.
    pub(crate) fn peek_binop_start(cursor: Cursor) -> bool {
        match cursor.punct() {
            Some((punct, _)) => matches!(
                punct.as_char(),
                '<' | '=' | '!' | '+' | '-' | '*' | '/' | '%' | '^' | '&' | '|' | '>'
            ),
            None => false,
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "parsing")))]
    impl Parse for BinOp {
        fn parse(input: ParseStream) -> Result<Self> {
            // Operators sharing a first character are tested in grammar order.
            let first = match input.cursor().punct() {
                Some((punct, _)) => punct.as_char(),
                None => return Err(input.error("expected binary operator")),
            };
            match first {
                '<' => {
                    if input.peek(Token![<==>]) {
                        return input.parse().map(BinOp::Equiv);
                    }
                    if input.peek(Token![<==]) {
                        return input.parse().map(BinOp::Exply);
                    }
                    if input.peek(Token![<<=]) {
                        return input.parse().map(BinOp::ShlAssign);
                    }
                    if input.peek(Token![<<]) {
                        return input.parse().map(BinOp::Shl);
                    }
                    if input.peek(Token![<=]) {
                        return input.parse().map(BinOp::Le);
                    }
                    if input.peek(Token![<]) {
                        return input.parse().map(BinOp::Lt);
                    }
                }
                '=' => {
                    if input.peek(Token![==>]) {
                        return input.parse().map(BinOp::Imply);
                    }
                    if input.peek(Token![===]) {
                        return input.parse().map(BinOp::BigEq);
                    }
                    if input.peek(Token![=~=]) {
                        return input.parse().map(BinOp::ExtEq);
                    }
                    if input.peek(Token![=~~=]) {
                        return input.parse().map(BinOp::ExtDeepEq);
                    }
                    if input.peek(Token![==]) {
                        return input.parse().map(BinOp::Eq);
                    }
                }
                '!' => {
                    if input.peek(Token![!==]) {
                        return input.parse().map(BinOp::BigNe);
                    }
                    if input.peek(Token![!~=]) {
                        return input.parse().map(BinOp::ExtNe);
                    }
                    if input.peek(Token![!~~=]) {
                        return input.parse().map(BinOp::ExtDeepNe);
                    }
                    if input.peek(Token![!=]) {
                        return input.parse().map(BinOp::Ne);
                    }
                }
                '+' => {
                    if input.peek(Token![+=]) {
                        return input.parse().map(BinOp::AddAssign);
                    }
                    if input.peek(Token![+]) {
                        return input.parse().map(BinOp::Add);
                    }
                }
                '-' => {
                    if input.peek(Token![-=]) {
                        return input.parse().map(BinOp::SubAssign);
                    }
                    if input.peek(Token![-]) {
                        return input.parse().map(BinOp::Sub);
                    }
                }
                '*' => {
                    if input.peek(Token![*=]) {
                        return input.parse().map(BinOp::MulAssign);
                    }
                    if input.peek(Token![*]) {
                        return input.parse().map(BinOp::Mul);
                    }
                }
                '/' => {
                    if input.peek(Token![/=]) {
                        return input.parse().map(BinOp::DivAssign);
                    }
                    if input.peek(Token![/]) {
                        return input.parse().map(BinOp::Div);
                    }
                }
                '%' => {
                    if input.peek(Token![%=]) {
                        return input.parse().map(BinOp::RemAssign);
                    }
                    if input.peek(Token![%]) {
                        return input.parse().map(BinOp::Rem);
                    }
                }
                '^' => {
                    if input.peek(Token![^=]) {
                        return input.parse().map(BinOp::BitXorAssign);
                    }
                    if input.peek(Token![^]) {
                        return input.parse().map(BinOp::BitXor);
                    }
                }
                '&' => {
                    if input.peek(Token![&=]) {
                        return input.parse().map(BinOp::BitAndAssign);
                    }
                    if input.peek(Token![&&]) {
                        return input.parse().map(BinOp::And);
                    }
                    if input.peek(Token![&]) {
                        return input.parse().map(BinOp::BitAnd);
                    }
                }
                '|' => {
                    if input.peek(Token![|=]) {
                        return input.parse().map(BinOp::BitOrAssign);
                    }
                    if input.peek(Token![||]) {
                        return input.parse().map(BinOp::Or);
                    }
                    if input.peek(Token![|]) {
                        return input.parse().map(BinOp::BitOr);
                    }
                }
                '>' => {
                    if input.peek(Token![>>=]) {
                        return input.parse().map(BinOp::ShrAssign);
                    }
                    if input.peek(Token![>>]) {
                        return input.parse().map(BinOp::Shr);
                    }
                    if input.peek(Token![>=]) {
                        return input.parse().map(BinOp::Ge);
                    }
                    if input.peek(Token![>]) {
                        return input.parse().map(BinOp::Gt);
                    }
                }
                _ => {}
            }
            Err(input.error("expected binary operator"))
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "parsing")))]
    impl Parse for UnOp {
        fn parse(input: ParseStream) -> Result<Self> {
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![*]) {
                input.parse().map(UnOp::Deref)
            } else if lookahead.peek(Token![!]) {
                input.parse().map(UnOp::Not)
            } else if lookahead.peek(Token![-]) {
                input.parse().map(UnOp::Neg)
            } else if lookahead.peek(Token![proof]) {
                input.parse().map(UnOp::Proof)
            } else if lookahead.peek(Token![forall]) {
                input.parse().map(UnOp::Forall)
            } else if lookahead.peek(Token![exists]) {
                input.parse().map(UnOp::Exists)
            } else if lookahead.peek(Token![choose]) {
                input.parse().map(UnOp::Choose)
            } else {
                Err(lookahead.error())
            }
        }
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::op::{BinOp, UnOp};
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for BinOp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                BinOp::Add(t) => t.to_tokens(tokens),
                BinOp::Sub(t) => t.to_tokens(tokens),
                BinOp::Mul(t) => t.to_tokens(tokens),
                BinOp::Div(t) => t.to_tokens(tokens),
                BinOp::Rem(t) => t.to_tokens(tokens),
                BinOp::And(t) => t.to_tokens(tokens),
                BinOp::Or(t) => t.to_tokens(tokens),
                BinOp::BitXor(t) => t.to_tokens(tokens),
                BinOp::BitAnd(t) => t.to_tokens(tokens),
                BinOp::BitOr(t) => t.to_tokens(tokens),
                BinOp::Shl(t) => t.to_tokens(tokens),
                BinOp::Shr(t) => t.to_tokens(tokens),
                BinOp::Eq(t) => t.to_tokens(tokens),
                BinOp::Lt(t) => t.to_tokens(tokens),
                BinOp::Le(t) => t.to_tokens(tokens),
                BinOp::Ne(t) => t.to_tokens(tokens),
                BinOp::Ge(t) => t.to_tokens(tokens),
                BinOp::Gt(t) => t.to_tokens(tokens),
                BinOp::AddAssign(t) => t.to_tokens(tokens),
                BinOp::SubAssign(t) => t.to_tokens(tokens),
                BinOp::MulAssign(t) => t.to_tokens(tokens),
                BinOp::DivAssign(t) => t.to_tokens(tokens),
                BinOp::RemAssign(t) => t.to_tokens(tokens),
                BinOp::BitXorAssign(t) => t.to_tokens(tokens),
                BinOp::BitAndAssign(t) => t.to_tokens(tokens),
                BinOp::BitOrAssign(t) => t.to_tokens(tokens),
                BinOp::ShlAssign(t) => t.to_tokens(tokens),
                BinOp::ShrAssign(t) => t.to_tokens(tokens),

                // verus
                BinOp::Equiv(t) => t.to_tokens(tokens),
                BinOp::Imply(t) => t.to_tokens(tokens),
                BinOp::Exply(t) => t.to_tokens(tokens),
                BinOp::BigEq(t) => t.to_tokens(tokens),
                BinOp::BigNe(t) => t.to_tokens(tokens),
                BinOp::ExtEq(t) => t.to_tokens(tokens),
                BinOp::ExtNe(t) => t.to_tokens(tokens),
                BinOp::ExtDeepEq(t) => t.to_tokens(tokens),
                BinOp::ExtDeepNe(t) => t.to_tokens(tokens),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UnOp {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                UnOp::Deref(t) => t.to_tokens(tokens),
                UnOp::Not(t) => t.to_tokens(tokens),
                UnOp::Neg(t) => t.to_tokens(tokens),

                // verus
                UnOp::Proof(t) => t.to_tokens(tokens),
                UnOp::Forall(t) => t.to_tokens(tokens),
                UnOp::Exists(t) => t.to_tokens(tokens),
                UnOp::Choose(t) => t.to_tokens(tokens),
            }
        }
    }
}
