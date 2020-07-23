#ifndef CREATEENCODING_H
#define CREATEENCODING_H

#pragma GCC diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#include <wx/wxprec.h>
#ifndef WX_PRECOMP
#include <wx/wx.h>
#endif
#pragma GCC diagnostic pop

#include "encoding.hpp"

wxSizer *createEncoding(Encoding *encoding, wxWindow *parent, bool boxed = true);
void updateEncoding(wxSizer *sizer, Encoding *encoding);

#endif
