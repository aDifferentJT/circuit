#include "../gui/encoding.hpp"

#include <functional>

extern "C"
Encoding* mkEncoding
  ( EncodingType type
  , int numChildren
  , const char* ident
  , int bit
  , Encoding* (*childAt)(void* idrisData, int i)
  , int editable
  , void (*flip)(void* idrisData)
  , void* idrisData
  ) {
  return new Encoding
    { type
    , numChildren
    , ident
    , bit
    , std::bind(childAt, idrisData, std::placeholders::_1)
    , editable
    , std::bind(flip, idrisData)
    };
}

