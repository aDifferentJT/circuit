#include "../gui/encoding.hpp"

#include <functional>

extern "C"
Encoding* mkEncoding
  ( int type
  , int numChildren
  , const char* ident
  , int bit
  , Encoding* (*childAt)(void* idrisData, int i)
  , int editable
  , void (*flip)(void* idrisData)
  , void* idrisData
  ) {
  return new Encoding
    { std::bind(childAt, idrisData, std::placeholders::_1)
    , std::bind(flip, idrisData)
    , static_cast<EncodingType>(type)
    , numChildren
    , ident
    , static_cast<bool>(bit)
    , static_cast<bool>(editable)
    };
}

