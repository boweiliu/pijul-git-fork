#![recursion_limit = "256"]
extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::*;

use std::iter::FromIterator;

fn name_capital(name: &str) -> String {
    name.chars()
        .enumerate()
        .map(|(i, s)| {
            if i == 0 {
                s.to_uppercase().next().unwrap()
            } else {
                s
            }
        })
        .collect()
}

#[proc_macro]
pub fn table(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    assert!(input_iter.next().is_none());
    let name_capital = syn::Ident::new(&name_capital(&name), Span::call_site());
    proc_macro::TokenStream::from(quote! {
        type #name_capital;
    })
}

#[proc_macro]
pub fn sanakirja_table_get(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let name_get = syn::Ident::new(&format!("get_{}", name), Span::call_site());
    let name = syn::Ident::new(&name, Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };

    let pre_ = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let pre = if !pre_.is_empty() {
        quote! {
            let (key, value) = #pre_;
        }
    } else {
        quote! {}
    };
    let post_ = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let post = if post_.is_empty() {
        quote! { if let Ok(x) = self.txn.get(&self.#name, key, value) {
            Ok(x)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }
        }
    } else {
        quote! { if let Ok(x) = self.txn.get(&self.#name, key, value) {
            Ok(x . #post_)
        } else {
            Err(TxnErr(SanakirjaError::PristineCorrupt))
        }}
    };
    proc_macro::TokenStream::from(quote! {
        fn #name_get <'txn> (&'txn self, key: #key, value: Option<#value>) -> Result<Option<#value>, TxnErr<Self::#error>> {
            use ::sanakirja::Transaction;
            #pre
            #post
        }
    })
}

#[proc_macro]
pub fn sanakirja_get(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let name_capital = syn::Ident::new(&name_capital(&name), Span::call_site());
    let name_get = syn::Ident::new(&format!("get_{}", name), Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };
    assert!(input_iter.next().is_none());
    proc_macro::TokenStream::from(quote! {
        fn #name_get(&self, db: &Self::#name_capital, key: #key, value: Option<#value>) -> Result<Option<#value>, TxnErr<Self::#error>> {
            use ::sanakirja::Transaction;
            if let Ok(x) = self.txn.get(db, key, value) {
                Ok(x)
            } else {
                Err(TxnErr(SanakirjaError::PristineCorrupt))
            }
        }
    })
}

#[proc_macro]
pub fn table_get(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let name_get = syn::Ident::new(&format!("get_{}", name), Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };
    assert!(input_iter.next().is_none());
    proc_macro::TokenStream::from(quote! {
        fn #name_get<'txn>(&'txn self, key: #key, value: Option<#value>) -> Result<Option<#value>, TxnErr<Self::#error>>;
    })
}

#[proc_macro]
pub fn get(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let name_capital = syn::Ident::new(&name_capital(&name), Span::call_site());
    let name_get = syn::Ident::new(&format!("get_{}", name), Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };
    assert!(input_iter.next().is_none());
    proc_macro::TokenStream::from(quote! {
        fn #name_get<'txn>(&'txn self, db: &Self::#name_capital, key: #key, value: Option<#value>) -> Result<Option<#value>, TxnErr<Self::#error>>;
    })
}

fn next(input_iter: &mut proc_macro2::token_stream::IntoIter) -> Vec<TokenTree> {
    let mut result = Vec::new();
    let mut is_first = true;
    loop {
        match input_iter.next() {
            Some(TokenTree::Punct(p)) => {
                if p.as_char() == ',' {
                    if !is_first {
                        return result;
                    }
                } else {
                    result.push(TokenTree::Punct(p))
                }
            }
            Some(e) => result.push(e),
            None => return result,
        }
        is_first = false
    }
}

#[proc_macro]
pub fn cursor(input: proc_macro::TokenStream) -> TokenStream {
    cursor_(input, false, false, false)
}

#[proc_macro]
pub fn cursor_ref(input: proc_macro::TokenStream) -> TokenStream {
    cursor_(input, false, false, true)
}

#[proc_macro]
pub fn iter(input: proc_macro::TokenStream) -> TokenStream {
    cursor_(input, false, true, false)
}

#[proc_macro]
pub fn rev_cursor(input: proc_macro::TokenStream) -> TokenStream {
    cursor_(input, true, false, false)
}

fn cursor_(input: proc_macro::TokenStream, rev: bool, iter: bool, borrow: bool) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let capital = name_capital(&name);
    let cursor_name = syn::Ident::new(&format!("{}Cursor", capital,), Span::call_site());
    let name_capital = syn::Ident::new(&name_capital(&name), Span::call_site());
    let name_iter = syn::Ident::new(&format!("iter_{}", name), Span::call_site());
    let name_next = syn::Ident::new(&format!("cursor_{}_next", name), Span::call_site());
    let name_prev = syn::Ident::new(&format!("cursor_{}_prev", name), Span::call_site());
    let name_cursor = syn::Ident::new(
        &format!("{}cursor_{}", if rev { "rev_" } else { "" }, name),
        Span::call_site(),
    );
    let name_cursor_ref = syn::Ident::new(
        &format!("{}cursor_{}_ref", if rev { "rev_" } else { "" }, name),
        Span::call_site(),
    );

    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { GraphError }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };

    let cursor_type = if rev {
        quote! {
            Result<crate::pristine::RevCursor<Self, &'txn Self, Self::#cursor_name, #key, #value>, TxnErr<Self::#error>>
        }
    } else {
        quote! {
            Result<crate::pristine::Cursor<Self, &'txn Self, Self::#cursor_name, #key, #value>, TxnErr<Self::#error>>
        }
    };
    let def = if rev {
        quote! {}
    } else {
        quote! {
            type #cursor_name;
            fn #name_next <'txn> (
                &'txn self,
                cursor: &mut Self::#cursor_name,
            ) -> Result<Option<(#key, #value)>, TxnErr<Self::#error>>;
            fn #name_prev <'txn> (
                &'txn self,
                cursor: &mut Self::#cursor_name,
            ) -> Result<Option<(#key, #value)>, TxnErr<Self::#error>>;
        }
    };
    let borrow = if borrow {
        quote! {
        fn #name_cursor_ref<RT: std::ops::Deref<Target = Self>>(
            txn: RT,
            db: &Self::#name_capital,
            pos: Option<(#key, Option<#value>)>,
        ) -> Result<crate::pristine::Cursor<Self, RT, Self::#cursor_name, #key, #value>, TxnErr<Self::#error>>;
        }
    } else {
        quote! {}
    };
    let iter = if !iter {
        quote! {}
    } else {
        quote! {
            fn #name_iter <'txn> (
                &'txn self,
                k: #key,
                v: Option<#value>
            ) -> #cursor_type;
        }
    };
    assert!(input_iter.next().is_none());
    proc_macro::TokenStream::from(quote! {
        #def
        fn #name_cursor<'txn>(
            &'txn self,
            db: &Self::#name_capital,
            pos: Option<(#key, Option<#value>)>,
        ) -> #cursor_type;
        #borrow
        #iter
    })
}

#[proc_macro]
pub fn sanakirja_cursor(input: proc_macro::TokenStream) -> TokenStream {
    sanakirja_cursor_(input, false, false, false)
}

#[proc_macro]
pub fn sanakirja_cursor_ref(input: proc_macro::TokenStream) -> TokenStream {
    sanakirja_cursor_(input, false, false, true)
}

#[proc_macro]
pub fn sanakirja_iter(input: proc_macro::TokenStream) -> TokenStream {
    sanakirja_cursor_(input, false, true, false)
}

#[proc_macro]
pub fn sanakirja_rev_cursor(input: proc_macro::TokenStream) -> TokenStream {
    sanakirja_cursor_(input, true, false, false)
}

fn sanakirja_cursor_(
    input: proc_macro::TokenStream,
    rev: bool,
    iter: bool,
    borrow: bool,
) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let cursor_name = syn::Ident::new(
        &format!("{}Cursor", name_capital(&name),),
        Span::call_site(),
    );

    let name_capital = syn::Ident::new(&name_capital(&name), Span::call_site());
    let name_next = syn::Ident::new(&format!("cursor_{}_next", name), Span::call_site());
    let name_prev = syn::Ident::new(&format!("cursor_{}_prev", name), Span::call_site());
    let name_cursor = syn::Ident::new(
        &format!("{}cursor_{}", if rev { "rev_" } else { "" }, name),
        Span::call_site(),
    );
    let name_cursor_ref = syn::Ident::new(
        &format!("{}cursor_{}_ref", if rev { "rev_" } else { "" }, name),
        Span::call_site(),
    );
    let name_iter = syn::Ident::new(
        &format!("{}iter_{}", if rev { "rev_" } else { "" }, name),
        Span::call_site(),
    );

    let name = syn::Ident::new(&name, Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    let pre = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let post = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let pre_init = if !pre.is_empty() {
        quote! { let pos = #pre; }
    } else {
        quote! {}
    };
    let post = if !post.is_empty() {
        quote! { . #post }
    } else {
        quote! {}
    };
    let iter = if iter {
        quote! {
            fn #name_iter <'txn> (
                &'txn self,
                k: #key,
                v: Option<#value>
            ) -> Result<Cursor<Self, &'txn Self, Self::#cursor_name, #key, #value>, TxnErr<SanakirjaError>> {
                self.#name_cursor(&self.#name, Some((k, v)))
            }
        }
    } else {
        quote! {}
    };

    let borrow = if borrow {
        quote! {
            fn #name_cursor_ref <RT: std::ops::Deref<Target = Self>> (
                txn: RT,
                db: &Self::#name_capital,
                pos: Option<(#key, Option<#value>)>,
            ) -> Result<Cursor<Self, RT, Self::#cursor_name, #key, #value>, TxnErr<SanakirjaError>> {
                #pre_init
                if let Ok((cursor, _)) = txn.txn.set_cursors(&db, pos) {
                    Ok(Cursor {
                        cursor,
                        txn,
                        marker: std::marker::PhantomData,
                    })
                } else {
                    Err(TxnErr(SanakirjaError::PristineCorrupt))
                }
            }
        }
    } else {
        quote! {}
    };

    proc_macro::TokenStream::from(if rev {
        quote! {
            fn #name_cursor<'txn>(
                &'txn self,
                db: &Self::#name_capital,
                pos: Option<(#key, Option<#value>)>,
            ) -> Result<super::RevCursor<Self, &'txn Self, Self::#cursor_name, #key, #value>, TxnErr<SanakirjaError>> {
                #pre_init
                let mut cursor = if pos.is_some() {
                    if let Ok((x, _)) = self.txn.set_cursors(&db, pos) {
                        x
                    } else {
                        return Err(TxnErr(SanakirjaError::PristineCorrupt))
                    }
                } else if let Ok(x) = self.txn.set_cursors_last(&db) {
                    x
                } else {
                    return Err(TxnErr(SanakirjaError::PristineCorrupt))
                };
                Ok(super::RevCursor {
                    cursor,
                    txn: self,
                    marker: std::marker::PhantomData,
                })
            }
        }
    } else {
        quote! {
            type #cursor_name = ::sanakirja::Cursor;
            fn #name_cursor<'txn>(
                &'txn self,
                db: &Self::#name_capital,
                pos: Option<(#key, Option<#value>)>,
            ) -> Result<Cursor<Self, &'txn Self, Self::#cursor_name, #key, #value>, TxnErr<SanakirjaError>> {
                #pre_init
                let mut cursor = if let Ok((x, _)) = self.txn.set_cursors(&db, pos) {
                    x
                } else {
                    return Err(TxnErr(SanakirjaError::PristineCorrupt))
                };
                Ok(Cursor {
                    cursor,
                    txn: self,
                    marker: std::marker::PhantomData,
                })
            }
            #borrow
            fn #name_next <'txn> (
                &'txn self,
                cursor: &mut Self::#cursor_name,
            ) -> Result<Option<(#key, #value)>, TxnErr<SanakirjaError>> {
                let x = if let Ok(x) = unsafe { ::sanakirja::next(&self.txn, cursor) } {
                    x
                } else {
                    return Err(TxnErr(SanakirjaError::PristineCorrupt))
                };
                Ok(x #post)
            }
            fn #name_prev <'txn> (
                &'txn self,
                cursor: &mut Self::#cursor_name,
            ) -> Result<Option<(#key, #value)>, TxnErr<SanakirjaError>> {
                let x = if let Ok(x) = unsafe { ::sanakirja::prev(&self.txn, cursor) } {
                    x
                } else {
                    return Err(TxnErr(SanakirjaError::PristineCorrupt))
                };
                Ok(x #post)
            }
            #iter
        }
    })
}

#[proc_macro]
pub fn initialized_cursor(input: proc_macro::TokenStream) -> TokenStream {
    initialized_cursor_(input, false)
}

#[proc_macro]
pub fn initialized_rev_cursor(input: proc_macro::TokenStream) -> TokenStream {
    initialized_cursor_(input, true)
}

fn initialized_cursor_(input: proc_macro::TokenStream, rev: bool) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let cursor_name = syn::Ident::new(
        &format!("{}Cursor", name_capital(&name),),
        Span::call_site(),
    );
    let name_next = syn::Ident::new(&format!("cursor_{}_next", name), Span::call_site());
    let name_prev = syn::Ident::new(&format!("cursor_{}_prev", name), Span::call_site());
    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    let txnt = next(&mut input_iter);
    let txnt: proc_macro2::TokenStream = if txnt.is_empty() {
        proc_macro2::TokenStream::from(quote! { TxnT })
    } else {
        proc_macro2::TokenStream::from_iter(txnt.into_iter())
    };

    let error = next(&mut input_iter);
    let error: proc_macro2::TokenStream = if error.is_empty() {
        proc_macro2::TokenStream::from(quote! { GraphError })
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };

    assert!(input_iter.next().is_none());
    if rev {
        proc_macro::TokenStream::from(quote! {
            impl<T: #txnt, RT: std::ops::Deref<Target = T>> Iterator for crate::pristine::RevCursor<T, RT, T::#cursor_name, #key, #value>
            {
                type Item = Result<(#key, #value), TxnErr<T::#error>>;
                fn next(&mut self) -> Option<Self::Item> {
                    match self.txn.#name_prev(&mut self.cursor) {
                        Ok(Some(x)) => Some(Ok(x)),
                        Ok(None) => None,
                        Err(e) => Some(Err(e)),
                    }
                }
            }
        })
    } else {
        proc_macro::TokenStream::from(quote! {

            impl<T: #txnt, RT: std::ops::Deref<Target = T>>
                crate::pristine::Cursor<T, RT, T::#cursor_name, #key, #value>
            {
                pub fn prev(&mut self) -> Option<Result<(#key, #value), TxnErr<T::#error>>> {
                    match self.txn.#name_prev(&mut self.cursor) {
                        Ok(Some(x)) => Some(Ok(x)),
                        Ok(None) => None,
                        Err(e) => Some(Err(e)),
                    }
                }
            }
            impl<T: #txnt, RT: std::ops::Deref<Target = T>> Iterator for crate::pristine::Cursor<T, RT, T::#cursor_name, #key, #value>
            {
                type Item = Result<(#key, #value), TxnErr<T::#error>>;
                fn next(&mut self) -> Option<Self::Item> {
                    match self.txn.#name_next(&mut self.cursor) {
                        Ok(Some(x)) => Some(Ok(x)),
                        Ok(None) => None,
                        Err(e) => Some(Err(e)),
                    }
                }
            }
        })
    }
}

#[proc_macro]
pub fn put_del(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let put = syn::Ident::new(&format!("put_{}", name), Span::call_site());
    let del = syn::Ident::new(&format!("del_{}", name), Span::call_site());

    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };
    assert!(input_iter.next().is_none());
    proc_macro::TokenStream::from(quote! {
        fn #put(
            &mut self,
            k: #key,
            e: #value,
        ) -> Result<bool, TxnErr<Self::#error>>;
        fn #del(
            &mut self,
            k: #key,
            e: Option<#value>,
        ) -> Result<bool, TxnErr<Self::#error>>;
    })
}

#[proc_macro]
pub fn sanakirja_put_del(input: proc_macro::TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let mut input_iter = input.into_iter();
    let name = match input_iter.next() {
        Some(TokenTree::Ident(id)) => id.to_string(),
        _ => panic!("txn_table: first argument not an identifier"),
    };
    let put = syn::Ident::new(&format!("put_{}", name), Span::call_site());
    let del = syn::Ident::new(&format!("del_{}", name), Span::call_site());
    let name = syn::Ident::new(&name, Span::call_site());

    let key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    let error = next(&mut input_iter);
    let error = if error.is_empty() {
        quote! { Error }
    } else {
        proc_macro2::TokenStream::from_iter(error.into_iter())
    };

    let pre_key = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());
    let pre_value = proc_macro2::TokenStream::from_iter(next(&mut input_iter).into_iter());

    assert!(input_iter.next().is_none());

    if pre_key.is_empty() {
        proc_macro::TokenStream::from(quote! {
            fn #put(
                &mut self,
                k: #key,
                v: #value,
            ) -> Result<bool, TxnErr<Self::#error>> {
                Ok(self.txn.put(&mut self.rng, &mut self.#name, k, v).map_err(TxnErr)?)
            }
            fn #del(
                &mut self,
                k: #key,
                v: Option<#value>,
            ) -> Result<bool, TxnErr<Self::#error>> {
                Ok(self.txn.del(&mut self.rng, &mut self.#name, k, v).map_err(TxnErr)?)
            }
        })
    } else {
        proc_macro::TokenStream::from(quote! {
            fn #put(
                &mut self,
                k: #key,
                v: #value,
            ) -> Result<bool, TxnErr<Self::#error>> {
                let k = #pre_key;
                let v = #pre_value;
                Ok(self.txn.put(&mut self.rng, &mut self.#name, k, v).map_err(TxnErr)?)
            }
            fn #del(
                &mut self,
                k: #key,
                v: Option<#value>,
            ) -> Result<bool, TxnErr<Self::#error>> {
                let k = #pre_key;
                let v = v.map(|v| #pre_value);
                Ok(self.txn.del(&mut self.rng, &mut self.#name, k, v).map_err(TxnErr)?)
            }
        })
    }
}
