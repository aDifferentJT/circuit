
struct Encoding;

typedef int EncodingType;
  
struct Encoding* mkEncoding
  ( EncodingType type
  , int numChildren
  , const char* ident
  , int bit
  , struct Encoding* (*childAt)(void* idrisData, int i)
  , int editable
  , void (*flip)(void* idrisData)
  , void* idrisData
  );

