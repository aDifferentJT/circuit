
#include "../gui/encoding.hpp"

extern "C"
Encoding* mkEncoding
  ( EncodingType type
  , int numChildren
  , const char* ident
  , int bit
  , Encoding* (*childAt)(int i)
  , int editable
  , void (*flip)()
  ) {
  return new Encoding
    { type
    , numChildren
    , ident
    , bit
    , childAt
    , editable
    , flip
    };
}

