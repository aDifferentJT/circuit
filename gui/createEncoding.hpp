#ifndef CREATEENCODING_H
#define CREATEENCODING_H

#include <wx/wxprec.h>
#ifndef WX_PRECOMP
#include <wx/wx.h>
#endif

#include "encoding.hpp"

wxSizer* createEncoding(Encoding* encoding, wxWindow* parent, bool boxed = true);
void updateEncoding(wxSizer* sizer, Encoding* encoding);

#endif
