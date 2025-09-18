extern crate proc_macro;

use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use syn::parse::{Parse, ParseStream};
use syn::{Data, DeriveInput, Index};

mod keyword {
    syn::custom_keyword!(skip);
}

enum MagicArgsAttribute {
    Skip,
}

impl Parse for MagicArgsAttribute {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();

        if lookahead.peek(keyword::skip) {
            let _skip: keyword::skip = input.parse()?;

            Ok(Self::Skip)
        } else {
            panic!("unknown attribute")
        }
    }
}

#[proc_macro_derive(MagicArgs, attributes(magic_args))]
pub fn magic_args_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let item = syn::parse_macro_input!(input as DeriveInput);

    let Data::Struct(data) = item.data else {
        panic!("MagicArgs can only be derived on structs")
    };

    let mut output = TokenStream::new();

    let mut types_seen = HashSet::new();

    for (idx, field) in data
        .fields
        .into_iter()
        .enumerate()
        .map(|(idx, field)| (Index::from(idx), field))
    {
        let mut skip = false;

        field
            .attrs
            .iter()
            .map(|attr| attr.parse_args().unwrap())
            .for_each(|attr: MagicArgsAttribute| match attr {
                MagicArgsAttribute::Skip { .. } => skip = true,
            });

        if skip {
            continue;
        }

        let field_type = field.ty;
        let item_name = item.ident.clone();

        let field_accessor = match field.ident {
            Some(ident) => ident.to_token_stream(),
            None => idx.to_token_stream(),
        };

        let (impl_generics, type_generics, where_clause) = item.generics.split_for_impl();

        output.extend(quote! {
            impl #impl_generics ::magic_args::Args< #field_type > for #item_name #type_generics
                #where_clause
            {
                #[inline]
                fn get(&self) -> #field_type {
                    ::core::clone::Clone::clone(&self.#field_accessor)
                }
            }
        });

        if !types_seen.insert(field_type) {
            panic!("MagicArgs cannot contain two items of the same type");
        }
    }

    quote! {
        const _: () = {
            #output
        };
    }
    .into()
}
