use crate::context::CodegenContext;
use crate::fields_gen::gen_parse_struct;
use crate::variants::{TransparentVariantView, VariantView, VariantsSet};
use proc_macro2::TokenStream;
use quote::quote;

impl<'a> VariantView<'a> {
    fn gen_parse(&self, ctx: &CodegenContext) -> TokenStream {
        let label = self.label;
        let variant_ident = self.ident;
        let ident = ctx.type_name;
        let parse_variant = gen_parse_struct(
            quote! { #ident::#variant_ident },
            ctx,
            self.fields,
            Some(label),
        );
        quote! {
            #label => {
                input = remaining;
                let result = (|| { #parse_variant })();
                return result.map_err(|err| match err {
                    error @ ::cmdparse::error::ParseFailure::Error(_) => error,
                    ::cmdparse::error::ParseFailure::Unrecognized(unrecognized) => unrecognized.into_error().into(),
                });
            }
        }
    }
}

impl<'a> TransparentVariantView<'a> {
    fn gen_parse(&self, ctx: &CodegenContext) -> TokenStream {
        let variant_ident = self.ident;
        let ident = ctx.type_name;
        let parse_variant =
            gen_parse_struct(quote! { #ident::#variant_ident }, ctx, self.fields, None);
        let error_handle = match self.ignore_error {
            true => quote!(Err(_) => {}),
            false => quote!(Err(error) => return Err(error)),
        };
        quote! {
            match (||{ #parse_variant })() {
                Ok(result) => return Ok(result),
                Err(::cmdparse::error::ParseFailure::Unrecognized(_)) => {},
                #error_handle
            }
        }
    }
}

pub(crate) fn gen_parse_enum(
    codegen_ctx: &CodegenContext<'_>,
    variants: &VariantsSet<'_>,
) -> TokenStream {
    let variants_parsing = variants
        .variant_views()
        .map(|variant| variant.gen_parse(codegen_ctx));

    let transparent_parsed = variants
        .transparent_variants()
        .map(|variant| variant.gen_parse(codegen_ctx));

    quote! {
        match input.take() {
            None => Err(::cmdparse::error::ParseError::token_required().expected("variant").into()),
            Some(Err(err)) => Err(err.into()),
            Some(Ok((token @ ::cmdparse::tokens::Token::Attribute(_), remaining))) => {
                Err(::cmdparse::error::UnrecognizedToken::new(token, remaining).into())
            }
            Some(Ok((token @ ::cmdparse::tokens::Token::Text(text) , remaining))) => {
                let text = text.parse_string();
                match ::std::borrow::Borrow::<str>::borrow(&text) {
                    #(#variants_parsing)*
                   _ => {
                        #(#transparent_parsed)*
                        Err(::cmdparse::error::UnrecognizedToken::new(token, remaining).into())
                    }
                }
            }
        }
    }
}
