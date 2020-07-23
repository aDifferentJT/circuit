
#include "../gui/encoding.hpp"

extern "C"
Encoding* mkEncoding
  ( int type
  , int numChildren
  , const char* ident
  , int bit
  , Encoding* (*childAt)(int i)
  , int editable
  , void (*flip)()
  ) {
  return new Encoding
    { childAt
    , flip
    , static_cast<EncodingType>(type)
    , numChildren
    , ident
    , static_cast<bool>(bit)
    , static_cast<bool>(editable)
    };
}

