/*
 Institute for Formal Models and Verification (FMV),
 Johannes Kepler University Linz, Austria
 
 Copyright (c) 2006, Robert Daniel Brummayer
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the FMV nor the names of its contributors may be
      used to endorse or promote products derived from this software without
      specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifdef HAVE_CONFIG_H
#  include <config.h>
#endif

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>

#include <gdk/gdkkeysyms.h>
#include <gtk/gtk.h>

#include "callbacks.h"
#include "interface.h"
#include "support.h"

#define GLADE_HOOKUP_OBJECT(component,widget,name) \
  g_object_set_data_full (G_OBJECT (component), name, \
    gtk_widget_ref (widget), (GDestroyNotify) gtk_widget_unref)

#define GLADE_HOOKUP_OBJECT_NO_REF(component,widget,name) \
  g_object_set_data (G_OBJECT (component), name, widget)

GtkWidget *
create_main_window (void)
{
  GSList *radiobutton_bits_group = NULL;
  GSList *radiobutton_no_dumping_group = NULL;
  GSList *radiobutton_output_mode_group = NULL;
  GSList *radiobutton_sat_group = NULL;
  GtkAccelGroup *accel_group;
  GtkWidget *about1;
  GtkWidget *alignment2;
  GtkWidget *alignment3;
  GtkWidget *alignment4;
  GtkWidget *alignment5;
  GtkWidget *alignment6;
  GtkWidget *alignment7;
  GtkWidget *alignment8;
  GtkWidget *alignment9;
  GtkWidget *button_run;
  GtkWidget *checkbutton_overflow;
  GtkWidget *checkbutton_verbose;
  GtkWidget *combobox_under_approx;
  GtkWidget *checkbutton_two_level_opt;
  GtkWidget *copy1;
  GtkWidget *cut1;
  GtkWidget *font1;
  GtkWidget *frame_bits;
  GtkWidget *frame_dumping;
  GtkWidget *frame_input;
  GtkWidget *frame_mode;
  GtkWidget *frame_output;
  GtkWidget *frame_output_mode;
  GtkWidget *frame_special_options;
  GtkWidget *go_to_line1;
  GtkWidget *hbox1;
  GtkWidget *hbox2;
  GtkWidget *image1;
  GtkWidget *image2;
  GtkWidget *label1;
  GtkWidget *label_bits;
  GtkWidget *label_dumping;
  GtkWidget *label_input;
  GtkWidget *label_mode;
  GtkWidget *label_output;
  GtkWidget *label_output_mode;
  GtkWidget *label_specialoptions;
  GtkWidget *main_window;
  GtkWidget *menubar1;
  GtkWidget *menuitem1;
  GtkWidget *menuitem1_menu;
  GtkWidget *menuitem2;
  GtkWidget *menuitem2_menu;
  GtkWidget *menuitem3;
  GtkWidget *menuitem3_menu;
  GtkWidget *menuitem4;
  GtkWidget *menuitem4_menu;
  GtkWidget *navigate1;
  GtkWidget *navigate1_menu;
  GtkWidget *new1;
  GtkWidget *open1;
  GtkWidget *paste1;
  GtkWidget *quit1;
  GtkWidget *radiobutton_16bits;
  GtkWidget *radiobutton_32bits;
  GtkWidget *radiobutton_4bits;
  GtkWidget *radiobutton_64bits;
  GtkWidget *radiobutton_8bits;
  GtkWidget *radiobutton_binary;
  GtkWidget *radiobutton_decimal;
  GtkWidget *radiobutton_dumpaig;
  GtkWidget *radiobutton_dumpcnf;
  GtkWidget *radiobutton_hexadecimal;
  GtkWidget *radiobutton_no_dumping;
  GtkWidget *radiobutton_sat;
  GtkWidget *radiobutton_taut;
  GtkWidget *radiobutton_defined;
  GtkWidget *radiobutton_undefined;
  GtkWidget *save1;
  GtkWidget *save_as1;
  GtkWidget *scrolledwindow1;
  GtkWidget *scrolledwindow2;
  GtkWidget *scrolledwindow3;
  GtkWidget *scrolledwindow4;
  GtkWidget *separatormenuitem1;
  GtkWidget *textview_input;
  GtkWidget *textview_output;
  GtkWidget *vbox1;
  GtkWidget *vbox2;
  GtkWidget *vbox3;
  GtkWidget *vbox4;
  GtkWidget *vbox5;
  GtkWidget *vbox6;
  GtkWidget *vbox7;
  GtkWidget *vbox8;
  GtkWidget *vbox9;
  GtkWidget *viewport1;
  GtkWidget *viewport2;
  GtkWidget *label_under_approx;
  GtkWidget *special_options_seperator;


  accel_group = gtk_accel_group_new ();

  main_window = gtk_window_new (GTK_WINDOW_TOPLEVEL);
  gtk_window_set_title (GTK_WINDOW (main_window), _("XC32SAT"));
  gtk_window_set_position (GTK_WINDOW (main_window), GTK_WIN_POS_CENTER);
  gtk_window_set_modal (GTK_WINDOW (main_window), TRUE);
  gtk_window_set_default_size (GTK_WINDOW (main_window), 800, 600);

  vbox1 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox1);
  gtk_container_add (GTK_CONTAINER (main_window), vbox1);

  menubar1 = gtk_menu_bar_new ();
  gtk_widget_show (menubar1);
  gtk_box_pack_start (GTK_BOX (vbox1), menubar1, FALSE, FALSE, 0);

  menuitem1 = gtk_menu_item_new_with_mnemonic (_("_File"));
  gtk_widget_show (menuitem1);
  gtk_container_add (GTK_CONTAINER (menubar1), menuitem1);

  menuitem1_menu = gtk_menu_new ();
  gtk_menu_item_set_submenu (GTK_MENU_ITEM (menuitem1), menuitem1_menu);

  new1 = gtk_image_menu_item_new_from_stock ("gtk-new", accel_group);
  gtk_widget_show (new1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), new1);

  open1 = gtk_image_menu_item_new_from_stock ("gtk-open", accel_group);
  gtk_widget_show (open1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), open1);

  save1 = gtk_image_menu_item_new_from_stock ("gtk-save", accel_group);
  gtk_widget_show (save1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), save1);

  save_as1 = gtk_image_menu_item_new_from_stock ("gtk-save-as", accel_group);
  gtk_widget_show (save_as1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), save_as1);

  separatormenuitem1 = gtk_separator_menu_item_new ();
  gtk_widget_show (separatormenuitem1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), separatormenuitem1);
  gtk_widget_set_sensitive (separatormenuitem1, FALSE);

  quit1 = gtk_image_menu_item_new_from_stock ("gtk-quit", accel_group);
  gtk_widget_show (quit1);
  gtk_container_add (GTK_CONTAINER (menuitem1_menu), quit1);

  menuitem2 = gtk_menu_item_new_with_mnemonic (_("_Edit"));
  gtk_widget_show (menuitem2);
  gtk_container_add (GTK_CONTAINER (menubar1), menuitem2);

  menuitem2_menu = gtk_menu_new ();
  gtk_menu_item_set_submenu (GTK_MENU_ITEM (menuitem2), menuitem2_menu);

  cut1 = gtk_image_menu_item_new_from_stock ("gtk-cut", accel_group);
  gtk_widget_show (cut1);
  gtk_container_add (GTK_CONTAINER (menuitem2_menu), cut1);

  copy1 = gtk_image_menu_item_new_from_stock ("gtk-copy", accel_group);
  gtk_widget_show (copy1);
  gtk_container_add (GTK_CONTAINER (menuitem2_menu), copy1);

  paste1 = gtk_image_menu_item_new_from_stock ("gtk-paste", accel_group);
  gtk_widget_show (paste1);
  gtk_container_add (GTK_CONTAINER (menuitem2_menu), paste1);

  menuitem3 = gtk_menu_item_new_with_mnemonic (_("_View"));
  gtk_widget_show (menuitem3);
  gtk_container_add (GTK_CONTAINER (menubar1), menuitem3);

  menuitem3_menu = gtk_menu_new ();
  gtk_menu_item_set_submenu (GTK_MENU_ITEM (menuitem3), menuitem3_menu);

  font1 = gtk_image_menu_item_new_from_stock ("gtk-select-font", accel_group);
  gtk_widget_show (font1);
  gtk_container_add (GTK_CONTAINER (menuitem3_menu), font1);

  navigate1 = gtk_menu_item_new_with_mnemonic (_("_Navigate"));
  gtk_widget_show (navigate1);
  gtk_container_add (GTK_CONTAINER (menubar1), navigate1);

  navigate1_menu = gtk_menu_new ();
  gtk_menu_item_set_submenu (GTK_MENU_ITEM (navigate1), navigate1_menu);

  go_to_line1 = gtk_image_menu_item_new_with_mnemonic (_("_Go To Line"));
  gtk_widget_show (go_to_line1);
  gtk_container_add (GTK_CONTAINER (navigate1_menu), go_to_line1);

  image2 = gtk_image_new_from_stock ("gtk-jump-to", GTK_ICON_SIZE_MENU);
  gtk_widget_show (image2);
  gtk_image_menu_item_set_image (GTK_IMAGE_MENU_ITEM (go_to_line1), image2);

  menuitem4 = gtk_menu_item_new_with_mnemonic (_("_Help"));
  gtk_widget_show (menuitem4);
  gtk_container_add (GTK_CONTAINER (menubar1), menuitem4);

  menuitem4_menu = gtk_menu_new ();
  gtk_menu_item_set_submenu (GTK_MENU_ITEM (menuitem4), menuitem4_menu);

  about1 = gtk_menu_item_new_with_mnemonic (_("_About"));
  gtk_widget_show (about1);
  gtk_container_add (GTK_CONTAINER (menuitem4_menu), about1);

  hbox1 = gtk_hbox_new (FALSE, 0);
  gtk_widget_show (hbox1);
  gtk_box_pack_start (GTK_BOX (vbox1), hbox1, TRUE, TRUE, 0);

  vbox2 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox2);
  gtk_box_pack_start (GTK_BOX (hbox1), vbox2, TRUE, TRUE, 10);

  scrolledwindow1 = gtk_scrolled_window_new (NULL, NULL);
  gtk_widget_show (scrolledwindow1);
  gtk_box_pack_start (GTK_BOX (vbox2), scrolledwindow1, TRUE, TRUE, 0);
  gtk_scrolled_window_set_policy (GTK_SCROLLED_WINDOW (scrolledwindow1),
                                  GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
  gtk_scrolled_window_set_shadow_type (GTK_SCROLLED_WINDOW (scrolledwindow1),
                                       GTK_SHADOW_IN);

  viewport1 = gtk_viewport_new (NULL, NULL);
  gtk_widget_show (viewport1);
  gtk_container_add (GTK_CONTAINER (scrolledwindow1), viewport1);

  frame_input = gtk_frame_new (NULL);
  gtk_widget_show (frame_input);
  gtk_container_add (GTK_CONTAINER (viewport1), frame_input);
  gtk_container_set_border_width (GTK_CONTAINER (frame_input), 1);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_input), GTK_SHADOW_ETCHED_OUT);

  alignment6 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment6);
  gtk_container_add (GTK_CONTAINER (frame_input), alignment6);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment6), 0, 0, 12, 0);

  scrolledwindow3 = gtk_scrolled_window_new (NULL, NULL);
  gtk_widget_show (scrolledwindow3);
  gtk_container_add (GTK_CONTAINER (alignment6), scrolledwindow3);
  gtk_scrolled_window_set_policy (GTK_SCROLLED_WINDOW (scrolledwindow3),
                                  GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
  gtk_scrolled_window_set_shadow_type (GTK_SCROLLED_WINDOW (scrolledwindow3),
                                       GTK_SHADOW_IN);

  textview_input = gtk_text_view_new ();
  gtk_widget_show (textview_input);
  gtk_container_add (GTK_CONTAINER (scrolledwindow3), textview_input);

  label_input = gtk_label_new (_("<b>Input</b>"));
  gtk_widget_show (label_input);
  gtk_frame_set_label_widget (GTK_FRAME (frame_input), label_input);
  gtk_label_set_use_markup (GTK_LABEL (label_input), TRUE);

  scrolledwindow2 = gtk_scrolled_window_new (NULL, NULL);
  gtk_widget_show (scrolledwindow2);
  gtk_box_pack_start (GTK_BOX (vbox2), scrolledwindow2, TRUE, TRUE, 0);
  gtk_scrolled_window_set_policy (GTK_SCROLLED_WINDOW (scrolledwindow2),
                                  GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
  gtk_scrolled_window_set_shadow_type (GTK_SCROLLED_WINDOW (scrolledwindow2),
                                       GTK_SHADOW_IN);

  viewport2 = gtk_viewport_new (NULL, NULL);
  gtk_widget_show (viewport2);
  gtk_container_add (GTK_CONTAINER (scrolledwindow2), viewport2);

  frame_output = gtk_frame_new (NULL);
  gtk_widget_show (frame_output);
  gtk_container_add (GTK_CONTAINER (viewport2), frame_output);
  gtk_container_set_border_width (GTK_CONTAINER (frame_output), 1);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_output), GTK_SHADOW_ETCHED_OUT);

  alignment7 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment7);
  gtk_container_add (GTK_CONTAINER (frame_output), alignment7);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment7), 0, 0, 12, 0);

  scrolledwindow4 = gtk_scrolled_window_new (NULL, NULL);
  gtk_widget_show (scrolledwindow4);
  gtk_container_add (GTK_CONTAINER (alignment7), scrolledwindow4);
  gtk_scrolled_window_set_policy (GTK_SCROLLED_WINDOW (scrolledwindow4),
                                  GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
  gtk_scrolled_window_set_shadow_type (GTK_SCROLLED_WINDOW (scrolledwindow4),
                                       GTK_SHADOW_IN);

  textview_output = gtk_text_view_new ();
  gtk_widget_show (textview_output);
  gtk_container_add (GTK_CONTAINER (scrolledwindow4), textview_output);
  gtk_text_view_set_editable (GTK_TEXT_VIEW (textview_output), FALSE);

  label_output = gtk_label_new (_("<b>Output</b>"));
  gtk_widget_show (label_output);
  gtk_frame_set_label_widget (GTK_FRAME (frame_output), label_output);
  gtk_label_set_use_markup (GTK_LABEL (label_output), TRUE);

  vbox3 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox3);
  gtk_box_pack_start (GTK_BOX (hbox1), vbox3, FALSE, TRUE, 10);

  vbox4 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox4);
  gtk_box_pack_start (GTK_BOX (vbox3), vbox4, TRUE, TRUE, 10);

  frame_mode = gtk_frame_new (NULL);
  gtk_widget_show (frame_mode);
  gtk_box_pack_start (GTK_BOX (vbox4), frame_mode, TRUE, TRUE, 0);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_mode), GTK_SHADOW_ETCHED_OUT);

  alignment5 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment5);
  gtk_container_add (GTK_CONTAINER (frame_mode), alignment5);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment5), 0, 0, 12, 0);

  vbox5 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox5);
  gtk_container_add (GTK_CONTAINER (alignment5), vbox5);

  radiobutton_sat =
    gtk_radio_button_new_with_mnemonic (NULL, _("Satisfiability"));
  gtk_widget_show (radiobutton_sat);
  gtk_box_pack_start (GTK_BOX (vbox5), radiobutton_sat, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_sat),
                              radiobutton_sat_group);
  radiobutton_sat_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_sat));

  radiobutton_taut =
    gtk_radio_button_new_with_mnemonic (NULL, _("Tautology"));
  gtk_widget_show (radiobutton_taut);
  gtk_box_pack_start (GTK_BOX (vbox5), radiobutton_taut, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_taut),
                              radiobutton_sat_group);
  radiobutton_sat_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_taut));

  radiobutton_defined =
    gtk_radio_button_new_with_mnemonic (NULL, _("Defined"));
  gtk_widget_show (radiobutton_defined);
  gtk_box_pack_start (GTK_BOX (vbox5), radiobutton_defined, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_defined),
                              radiobutton_sat_group);
  radiobutton_sat_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_defined));

  radiobutton_undefined =
    gtk_radio_button_new_with_mnemonic (NULL, _("Undefined"));
  gtk_widget_show (radiobutton_undefined);
  gtk_box_pack_start (GTK_BOX (vbox5), radiobutton_undefined, FALSE, FALSE,
                      0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_undefined),
                              radiobutton_sat_group);
  radiobutton_sat_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_undefined));

  label_mode = gtk_label_new (_("<b>Mode</b>"));
  gtk_widget_show (label_mode);
  gtk_frame_set_label_widget (GTK_FRAME (frame_mode), label_mode);
  gtk_label_set_use_markup (GTK_LABEL (label_mode), TRUE);

  frame_bits = gtk_frame_new (NULL);
  gtk_widget_show (frame_bits);
  gtk_box_pack_start (GTK_BOX (vbox4), frame_bits, TRUE, TRUE, 0);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_bits), GTK_SHADOW_ETCHED_OUT);

  alignment4 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment4);
  gtk_container_add (GTK_CONTAINER (frame_bits), alignment4);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment4), 0, 0, 12, 0);

  vbox6 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox6);
  gtk_container_add (GTK_CONTAINER (alignment4), vbox6);

  radiobutton_4bits = gtk_radio_button_new_with_mnemonic (NULL, _("4 Bits"));
  gtk_widget_show (radiobutton_4bits);
  gtk_box_pack_start (GTK_BOX (vbox6), radiobutton_4bits, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_4bits),
                              radiobutton_bits_group);
  radiobutton_bits_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_4bits));

  radiobutton_8bits = gtk_radio_button_new_with_mnemonic (NULL, _("8 Bits"));
  gtk_widget_show (radiobutton_8bits);
  gtk_box_pack_start (GTK_BOX (vbox6), radiobutton_8bits, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_8bits),
                              radiobutton_bits_group);
  radiobutton_bits_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_8bits));

  radiobutton_16bits =
    gtk_radio_button_new_with_mnemonic (NULL, _("16 Bits"));
  gtk_widget_show (radiobutton_16bits);
  gtk_box_pack_start (GTK_BOX (vbox6), radiobutton_16bits, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_16bits),
                              radiobutton_bits_group);
  radiobutton_bits_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_16bits));

  radiobutton_32bits =
    gtk_radio_button_new_with_mnemonic (NULL, _("32 Bits"));
  gtk_widget_show (radiobutton_32bits);
  gtk_box_pack_start (GTK_BOX (vbox6), radiobutton_32bits, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_32bits),
                              radiobutton_bits_group);
  radiobutton_bits_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_32bits));

  radiobutton_64bits =
    gtk_radio_button_new_with_mnemonic (NULL, _("64 Bits"));
  gtk_widget_show (radiobutton_64bits);
  gtk_box_pack_start (GTK_BOX (vbox6), radiobutton_64bits, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_64bits),
                              radiobutton_bits_group);
  radiobutton_bits_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_64bits));

  gtk_button_clicked (GTK_BUTTON (radiobutton_32bits));

  label_bits = gtk_label_new (_("<b>Number of Bits</b>"));
  gtk_widget_show (label_bits);
  gtk_frame_set_label_widget (GTK_FRAME (frame_bits), label_bits);
  gtk_label_set_use_markup (GTK_LABEL (label_bits), TRUE);

  frame_output_mode = gtk_frame_new (NULL);
  gtk_widget_show (frame_output_mode);
  gtk_box_pack_start (GTK_BOX (vbox4), frame_output_mode, TRUE, TRUE, 0);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_output_mode),
                             GTK_SHADOW_ETCHED_OUT);

  alignment9 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment9);
  gtk_container_add (GTK_CONTAINER (frame_output_mode), alignment9);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment9), 0, 0, 12, 0);

  vbox9 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox9);
  gtk_container_add (GTK_CONTAINER (alignment9), vbox9);

  radiobutton_binary = gtk_radio_button_new_with_mnemonic (NULL, _("Binary"));
  gtk_widget_show (radiobutton_binary);
  gtk_box_pack_start (GTK_BOX (vbox9), radiobutton_binary, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_binary),
                              radiobutton_output_mode_group);
  radiobutton_output_mode_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_binary));

  radiobutton_decimal =
    gtk_radio_button_new_with_mnemonic (NULL, _("Decimal"));
  gtk_widget_show (radiobutton_decimal);
  gtk_box_pack_start (GTK_BOX (vbox9), radiobutton_decimal, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_decimal),
                              radiobutton_output_mode_group);
  radiobutton_output_mode_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_decimal));

  radiobutton_hexadecimal =
    gtk_radio_button_new_with_mnemonic (NULL, _("Hexadecimal"));
  gtk_widget_show (radiobutton_hexadecimal);
  gtk_box_pack_start (GTK_BOX (vbox9), radiobutton_hexadecimal, FALSE, FALSE,
                      0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_hexadecimal),
                              radiobutton_output_mode_group);
  radiobutton_output_mode_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_hexadecimal));

  gtk_button_clicked (GTK_BUTTON (radiobutton_decimal));

  label_output_mode = gtk_label_new (_("<b>Output Mode</b>"));
  gtk_widget_show (label_output_mode);
  gtk_frame_set_label_widget (GTK_FRAME (frame_output_mode),
                              label_output_mode);
  gtk_label_set_use_markup (GTK_LABEL (label_output_mode), TRUE);

  frame_dumping = gtk_frame_new (NULL);
  gtk_widget_show (frame_dumping);
  gtk_box_pack_start (GTK_BOX (vbox4), frame_dumping, TRUE, TRUE, 0);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_dumping),
                             GTK_SHADOW_ETCHED_OUT);

  alignment2 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment2);
  gtk_container_add (GTK_CONTAINER (frame_dumping), alignment2);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment2), 0, 0, 12, 0);

  vbox8 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox8);
  gtk_container_add (GTK_CONTAINER (alignment2), vbox8);

  radiobutton_no_dumping =
    gtk_radio_button_new_with_mnemonic (NULL, _("None"));
  gtk_widget_show (radiobutton_no_dumping);
  gtk_box_pack_start (GTK_BOX (vbox8), radiobutton_no_dumping, FALSE, FALSE,
                      0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_no_dumping),
                              radiobutton_no_dumping_group);
  radiobutton_no_dumping_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_no_dumping));

  radiobutton_dumpcnf =
    gtk_radio_button_new_with_mnemonic (NULL, _("Dump CNF"));
  gtk_widget_show (radiobutton_dumpcnf);
  gtk_box_pack_start (GTK_BOX (vbox8), radiobutton_dumpcnf, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_dumpcnf),
                              radiobutton_no_dumping_group);
  radiobutton_no_dumping_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_dumpcnf));

  radiobutton_dumpaig =
    gtk_radio_button_new_with_mnemonic (NULL, _("Dump AIG"));
  gtk_widget_show (radiobutton_dumpaig);
  gtk_box_pack_start (GTK_BOX (vbox8), radiobutton_dumpaig, FALSE, FALSE, 0);
  gtk_radio_button_set_group (GTK_RADIO_BUTTON (radiobutton_dumpaig),
                              radiobutton_no_dumping_group);
  radiobutton_no_dumping_group =
    gtk_radio_button_get_group (GTK_RADIO_BUTTON (radiobutton_dumpaig));

  label_dumping = gtk_label_new (_("<b>Dumping Options</b>"));
  gtk_widget_show (label_dumping);
  gtk_frame_set_label_widget (GTK_FRAME (frame_dumping), label_dumping);
  gtk_label_set_use_markup (GTK_LABEL (label_dumping), TRUE);

  frame_special_options = gtk_frame_new (NULL);
  gtk_widget_show (frame_special_options);
  gtk_box_pack_start (GTK_BOX (vbox4), frame_special_options, TRUE, TRUE, 0);
  gtk_frame_set_shadow_type (GTK_FRAME (frame_special_options),
                             GTK_SHADOW_ETCHED_OUT);

  alignment3 = gtk_alignment_new (0.5, 0.5, 1, 1);
  gtk_widget_show (alignment3);
  gtk_container_add (GTK_CONTAINER (frame_special_options), alignment3);
  gtk_alignment_set_padding (GTK_ALIGNMENT (alignment3), 0, 0, 12, 0);

  vbox7 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox7);
  gtk_container_add (GTK_CONTAINER (alignment3), vbox7);

  checkbutton_two_level_opt =
    gtk_check_button_new_with_mnemonic (_("Two level opt."));
  gtk_widget_show (checkbutton_two_level_opt);
  gtk_box_pack_start (GTK_BOX (vbox7), checkbutton_two_level_opt, FALSE,
                      FALSE, 0);

  checkbutton_overflow =
    gtk_check_button_new_with_mnemonic (_("Allow Overflow"));
  gtk_widget_show (checkbutton_overflow);
  gtk_box_pack_start (GTK_BOX (vbox7), checkbutton_overflow, FALSE, FALSE, 0);

  checkbutton_verbose =
    gtk_check_button_new_with_mnemonic (_("Verbose Output"));
  gtk_widget_show (checkbutton_verbose);
  gtk_box_pack_start (GTK_BOX (vbox7), checkbutton_verbose, FALSE, FALSE, 0);

  special_options_seperator = gtk_hseparator_new();
  gtk_widget_show (special_options_seperator);
  gtk_box_pack_start (GTK_BOX (vbox7), special_options_seperator, FALSE, FALSE, 0);

  label_under_approx = gtk_label_new("Under-approx.");
  gtk_misc_set_alignment (GTK_MISC(label_under_approx), 0.0, 0.0);
  gtk_widget_show (label_under_approx);
  gtk_box_pack_start (GTK_BOX (vbox7), label_under_approx, FALSE, FALSE, 0);

  combobox_under_approx = gtk_combo_box_new_text();
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "None");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "1");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "2");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "4");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "8");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "16");
  gtk_combo_box_append_text (GTK_COMBO_BOX(combobox_under_approx), "32");
  gtk_combo_box_set_active (GTK_COMBO_BOX(combobox_under_approx), 1);
  gtk_widget_show (combobox_under_approx);
  gtk_box_pack_start (GTK_BOX (vbox7), combobox_under_approx, FALSE, FALSE, 0);

  label_specialoptions = gtk_label_new (_("<b>Special Options</b>"));
  gtk_widget_show (label_specialoptions);
  gtk_frame_set_label_widget (GTK_FRAME (frame_special_options),
                              label_specialoptions);
  gtk_label_set_use_markup (GTK_LABEL (label_specialoptions), TRUE);

  gtk_button_clicked (GTK_BUTTON (checkbutton_two_level_opt));

  button_run = gtk_button_new ();
  gtk_widget_show (button_run);
  gtk_box_pack_start (GTK_BOX (vbox3), button_run, FALSE, FALSE, 14);

  alignment8 = gtk_alignment_new (0.5, 0.5, 0, 0);
  gtk_widget_show (alignment8);
  gtk_container_add (GTK_CONTAINER (button_run), alignment8);

  hbox2 = gtk_hbox_new (FALSE, 2);
  gtk_widget_show (hbox2);
  gtk_container_add (GTK_CONTAINER (alignment8), hbox2);

  image1 = gtk_image_new_from_stock ("gtk-execute", GTK_ICON_SIZE_BUTTON);
  gtk_widget_show (image1);
  gtk_box_pack_start (GTK_BOX (hbox2), image1, FALSE, FALSE, 0);

  label1 = gtk_label_new_with_mnemonic (_("Run C32SAT"));
  gtk_widget_show (label1);
  gtk_box_pack_start (GTK_BOX (hbox2), label1, FALSE, FALSE, 0);

  g_signal_connect ((gpointer) main_window, "destroy",
                    G_CALLBACK (on_main_window_destroy), NULL);
  g_signal_connect ((gpointer) main_window, "delete_event",
                    G_CALLBACK (on_main_window_delete_event), NULL);
  g_signal_connect ((gpointer) new1, "activate",
                    G_CALLBACK (on_new1_activate), NULL);
  g_signal_connect ((gpointer) open1, "activate",
                    G_CALLBACK (on_open1_activate), NULL);
  g_signal_connect ((gpointer) save1, "activate",
                    G_CALLBACK (on_save1_activate), NULL);
  g_signal_connect ((gpointer) save_as1, "activate",
                    G_CALLBACK (on_save_as1_activate), NULL);
  g_signal_connect ((gpointer) quit1, "activate",
                    G_CALLBACK (on_quit1_activate), NULL);
  g_signal_connect ((gpointer) cut1, "activate",
                    G_CALLBACK (on_cut1_activate), NULL);
  g_signal_connect ((gpointer) copy1, "activate",
                    G_CALLBACK (on_copy1_activate), NULL);
  g_signal_connect ((gpointer) paste1, "activate",
                    G_CALLBACK (on_paste1_activate), NULL);
  g_signal_connect ((gpointer) font1, "activate",
                    G_CALLBACK (on_font1_activate), NULL);
  g_signal_connect ((gpointer) go_to_line1, "activate",
                    G_CALLBACK (on_go_to_line1_activate), NULL);
  g_signal_connect ((gpointer) about1, "activate",
                    G_CALLBACK (on_about1_activate), NULL);
  g_signal_connect ((gpointer) button_run, "button_release_event",
                    G_CALLBACK (on_button_run_button_release_event), NULL);
  g_signal_connect ((gpointer) radiobutton_sat, "button_release_event",
                    G_CALLBACK (on_radiobutton_mode_release_event), NULL);
  g_signal_connect ((gpointer) radiobutton_taut, "button_release_event",
                    G_CALLBACK (on_radiobutton_mode_release_event), NULL);
  g_signal_connect ((gpointer) radiobutton_defined, "button_release_event",
                    G_CALLBACK (on_radiobutton_mode_release_event), NULL);
  g_signal_connect ((gpointer) radiobutton_undefined, "button_release_event",
                    G_CALLBACK (on_radiobutton_mode_release_event), NULL);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (main_window, main_window, "main_window");
  GLADE_HOOKUP_OBJECT (main_window, vbox1, "vbox1");
  GLADE_HOOKUP_OBJECT (main_window, menubar1, "menubar1");
  GLADE_HOOKUP_OBJECT (main_window, menuitem1, "menuitem1");
  GLADE_HOOKUP_OBJECT (main_window, menuitem1_menu, "menuitem1_menu");
  GLADE_HOOKUP_OBJECT (main_window, new1, "new1");
  GLADE_HOOKUP_OBJECT (main_window, open1, "open1");
  GLADE_HOOKUP_OBJECT (main_window, save1, "save1");
  GLADE_HOOKUP_OBJECT (main_window, save_as1, "save_as1");
  GLADE_HOOKUP_OBJECT (main_window, separatormenuitem1, "separatormenuitem1");
  GLADE_HOOKUP_OBJECT (main_window, quit1, "quit1");
  GLADE_HOOKUP_OBJECT (main_window, menuitem2, "menuitem2");
  GLADE_HOOKUP_OBJECT (main_window, menuitem2_menu, "menuitem2_menu");
  GLADE_HOOKUP_OBJECT (main_window, cut1, "cut1");
  GLADE_HOOKUP_OBJECT (main_window, copy1, "copy1");
  GLADE_HOOKUP_OBJECT (main_window, paste1, "paste1");
  GLADE_HOOKUP_OBJECT (main_window, menuitem3, "menuitem3");
  GLADE_HOOKUP_OBJECT (main_window, menuitem3_menu, "menuitem3_menu");
  GLADE_HOOKUP_OBJECT (main_window, font1, "font1");
  GLADE_HOOKUP_OBJECT (main_window, navigate1, "navigate1");
  GLADE_HOOKUP_OBJECT (main_window, navigate1_menu, "navigate1_menu");
  GLADE_HOOKUP_OBJECT (main_window, go_to_line1, "go_to_line1");
  GLADE_HOOKUP_OBJECT (main_window, image2, "image2");
  GLADE_HOOKUP_OBJECT (main_window, menuitem4, "menuitem4");
  GLADE_HOOKUP_OBJECT (main_window, menuitem4_menu, "menuitem4_menu");
  GLADE_HOOKUP_OBJECT (main_window, about1, "about1");
  GLADE_HOOKUP_OBJECT (main_window, hbox1, "hbox1");
  GLADE_HOOKUP_OBJECT (main_window, vbox2, "vbox2");
  GLADE_HOOKUP_OBJECT (main_window, scrolledwindow1, "scrolledwindow1");
  GLADE_HOOKUP_OBJECT (main_window, viewport1, "viewport1");
  GLADE_HOOKUP_OBJECT (main_window, frame_input, "frame_input");
  GLADE_HOOKUP_OBJECT (main_window, alignment6, "alignment6");
  GLADE_HOOKUP_OBJECT (main_window, scrolledwindow3, "scrolledwindow3");
  GLADE_HOOKUP_OBJECT (main_window, textview_input, "textview_input");
  GLADE_HOOKUP_OBJECT (main_window, label_input, "label_input");
  GLADE_HOOKUP_OBJECT (main_window, scrolledwindow2, "scrolledwindow2");
  GLADE_HOOKUP_OBJECT (main_window, viewport2, "viewport2");
  GLADE_HOOKUP_OBJECT (main_window, frame_output, "frame_output");
  GLADE_HOOKUP_OBJECT (main_window, alignment7, "alignment7");
  GLADE_HOOKUP_OBJECT (main_window, scrolledwindow4, "scrolledwindow4");
  GLADE_HOOKUP_OBJECT (main_window, textview_output, "textview_output");
  GLADE_HOOKUP_OBJECT (main_window, label_output, "label_output");
  GLADE_HOOKUP_OBJECT (main_window, label_under_approx, "label_under_approx");
  GLADE_HOOKUP_OBJECT (main_window, vbox3, "vbox3");
  GLADE_HOOKUP_OBJECT (main_window, vbox4, "vbox4");
  GLADE_HOOKUP_OBJECT (main_window, frame_mode, "frame_mode");
  GLADE_HOOKUP_OBJECT (main_window, alignment5, "alignment5");
  GLADE_HOOKUP_OBJECT (main_window, vbox5, "vbox5");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_sat, "radiobutton_sat");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_taut, "radiobutton_taut");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_defined,
                       "radiobutton_defined");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_undefined,
                       "radiobutton_undefined");
  GLADE_HOOKUP_OBJECT (main_window, label_mode, "label_mode");
  GLADE_HOOKUP_OBJECT (main_window, frame_bits, "frame_bits");
  GLADE_HOOKUP_OBJECT (main_window, alignment4, "alignment4");
  GLADE_HOOKUP_OBJECT (main_window, vbox6, "vbox6");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_4bits, "radiobutton_4bits");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_8bits, "radiobutton_8bits");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_16bits, "radiobutton_16bits");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_32bits, "radiobutton_32bits");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_64bits, "radiobutton_64bits");
  GLADE_HOOKUP_OBJECT (main_window, label_bits, "label_bits");

  GLADE_HOOKUP_OBJECT (main_window, frame_output_mode, "frame_output_mode");
  GLADE_HOOKUP_OBJECT (main_window, alignment9, "alignment9");
  GLADE_HOOKUP_OBJECT (main_window, vbox9, "vbox9");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_binary, "radiobutton_binary");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_decimal,
                       "radiobutton_decimal");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_hexadecimal,
                       "radiobutton_hexadecimal");
  GLADE_HOOKUP_OBJECT (main_window, label_output_mode, "label_output_mode");

  GLADE_HOOKUP_OBJECT (main_window, frame_dumping, "frame_dumping");
  GLADE_HOOKUP_OBJECT (main_window, alignment2, "alignment2");
  GLADE_HOOKUP_OBJECT (main_window, vbox8, "vbox8");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_no_dumping,
                       "radiobutton_no_dumping");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_dumpcnf,
                       "radiobutton_dumpcnf");
  GLADE_HOOKUP_OBJECT (main_window, radiobutton_dumpaig,
                       "radiobutton_dumpaig");
  GLADE_HOOKUP_OBJECT (main_window, label_dumping, "label_dumping");
  GLADE_HOOKUP_OBJECT (main_window, frame_special_options,
                       "frame_special_options");
  GLADE_HOOKUP_OBJECT (main_window, alignment3, "alignment3");
  GLADE_HOOKUP_OBJECT (main_window, vbox7, "vbox7");
  GLADE_HOOKUP_OBJECT (main_window, checkbutton_overflow,
                       "checkbutton_overflow");
  GLADE_HOOKUP_OBJECT (main_window, checkbutton_verbose,
                       "checkbutton_verbose");
  GLADE_HOOKUP_OBJECT (main_window, combobox_under_approx,
                       "combobox_under_approx");
  GLADE_HOOKUP_OBJECT (main_window, checkbutton_two_level_opt,
                       "checkbutton_two_level_opt");
  GLADE_HOOKUP_OBJECT (main_window, label_specialoptions,
                       "label_specialoptions");
  GLADE_HOOKUP_OBJECT (main_window, button_run, "button_run");
  GLADE_HOOKUP_OBJECT (main_window, alignment8, "alignment8");
  GLADE_HOOKUP_OBJECT (main_window, hbox2, "hbox2");
  GLADE_HOOKUP_OBJECT (main_window, image1, "image1");
  GLADE_HOOKUP_OBJECT (main_window, label1, "label1");

  gtk_window_add_accel_group (GTK_WINDOW (main_window), accel_group);

  return main_window;
}

GtkWidget *
create_filechooserdialog_open (void)
{
  GtkWidget *filechooserdialog_open;
  GtkWidget *dialog_vbox2;
  GtkWidget *dialog_action_area2;
  GtkWidget *filechooserdialog_open_button_cancel;
  GtkWidget *filechooserdialog_open_button_open;

  filechooserdialog_open =
    gtk_file_chooser_dialog_new (_("Open File"), NULL,
                                 GTK_FILE_CHOOSER_ACTION_OPEN, NULL);
  gtk_window_set_position (GTK_WINDOW (filechooserdialog_open),
                           GTK_WIN_POS_CENTER);
  gtk_window_set_modal (GTK_WINDOW (filechooserdialog_open), TRUE);
  gtk_window_set_type_hint (GTK_WINDOW (filechooserdialog_open),
                            GDK_WINDOW_TYPE_HINT_DIALOG);

  dialog_vbox2 = GTK_DIALOG (filechooserdialog_open)->vbox;
  gtk_widget_show (dialog_vbox2);

  dialog_action_area2 = GTK_DIALOG (filechooserdialog_open)->action_area;
  gtk_widget_show (dialog_action_area2);
  gtk_button_box_set_layout (GTK_BUTTON_BOX (dialog_action_area2),
                             GTK_BUTTONBOX_END);

  filechooserdialog_open_button_cancel =
    gtk_button_new_from_stock ("gtk-cancel");
  gtk_widget_show (filechooserdialog_open_button_cancel);
  gtk_dialog_add_action_widget (GTK_DIALOG (filechooserdialog_open),
                                filechooserdialog_open_button_cancel,
                                GTK_RESPONSE_CANCEL);
  GTK_WIDGET_SET_FLAGS (filechooserdialog_open_button_cancel,
                        GTK_CAN_DEFAULT);

  filechooserdialog_open_button_open = gtk_button_new_from_stock ("gtk-open");
  gtk_widget_show (filechooserdialog_open_button_open);
  gtk_dialog_add_action_widget (GTK_DIALOG (filechooserdialog_open),
                                filechooserdialog_open_button_open,
                                GTK_RESPONSE_OK);
  GTK_WIDGET_SET_FLAGS (filechooserdialog_open_button_open, GTK_CAN_DEFAULT);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_open, filechooserdialog_open,
                              "filechooserdialog_open");
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_open, dialog_vbox2,
                              "dialog_vbox2");
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_open, dialog_action_area2,
                              "dialog_action_area2");
  GLADE_HOOKUP_OBJECT (filechooserdialog_open,
                       filechooserdialog_open_button_cancel,
                       "filechooserdialog_open_button_cancel");
  GLADE_HOOKUP_OBJECT (filechooserdialog_open,
                       filechooserdialog_open_button_open,
                       "filechooserdialog_open_button_open");

  gtk_widget_grab_default (filechooserdialog_open_button_open);
  return filechooserdialog_open;
}

GtkWidget *
create_filechooserdialog_save (void)
{
  GtkWidget *filechooserdialog_save;
  GtkWidget *dialog_vbox3;
  GtkWidget *dialog_action_area3;
  GtkWidget *filechooserdialog_save_button_cancel;
  GtkWidget *filechooserdialog_save_button_save;

  filechooserdialog_save =
    gtk_file_chooser_dialog_new (_("Save File"), NULL,
                                 GTK_FILE_CHOOSER_ACTION_SAVE, NULL);
  gtk_window_set_position (GTK_WINDOW (filechooserdialog_save),
                           GTK_WIN_POS_CENTER);
  gtk_window_set_modal (GTK_WINDOW (filechooserdialog_save), TRUE);
  gtk_window_set_type_hint (GTK_WINDOW (filechooserdialog_save),
                            GDK_WINDOW_TYPE_HINT_DIALOG);

  dialog_vbox3 = GTK_DIALOG (filechooserdialog_save)->vbox;
  gtk_widget_show (dialog_vbox3);

  dialog_action_area3 = GTK_DIALOG (filechooserdialog_save)->action_area;
  gtk_widget_show (dialog_action_area3);
  gtk_button_box_set_layout (GTK_BUTTON_BOX (dialog_action_area3),
                             GTK_BUTTONBOX_END);

  filechooserdialog_save_button_cancel =
    gtk_button_new_from_stock ("gtk-cancel");
  gtk_widget_show (filechooserdialog_save_button_cancel);
  gtk_dialog_add_action_widget (GTK_DIALOG (filechooserdialog_save),
                                filechooserdialog_save_button_cancel,
                                GTK_RESPONSE_CANCEL);
  GTK_WIDGET_SET_FLAGS (filechooserdialog_save_button_cancel,
                        GTK_CAN_DEFAULT);

  filechooserdialog_save_button_save = gtk_button_new_from_stock ("gtk-save");
  gtk_widget_show (filechooserdialog_save_button_save);
  gtk_dialog_add_action_widget (GTK_DIALOG (filechooserdialog_save),
                                filechooserdialog_save_button_save,
                                GTK_RESPONSE_OK);
  GTK_WIDGET_SET_FLAGS (filechooserdialog_save_button_save, GTK_CAN_DEFAULT);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_save, filechooserdialog_save,
                              "filechooserdialog_save");
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_save, dialog_vbox3,
                              "dialog_vbox3");
  GLADE_HOOKUP_OBJECT_NO_REF (filechooserdialog_save, dialog_action_area3,
                              "dialog_action_area3");
  GLADE_HOOKUP_OBJECT (filechooserdialog_save,
                       filechooserdialog_save_button_cancel,
                       "filechooserdialog_save_button_cancel");
  GLADE_HOOKUP_OBJECT (filechooserdialog_save,
                       filechooserdialog_save_button_save,
                       "filechooserdialog_save_button_save");

  gtk_widget_grab_default (filechooserdialog_save_button_save);
  return filechooserdialog_save;
}

GtkWidget *
create_fontselectiondialog (void)
{
  GtkWidget *fontselectiondialog;
  GtkWidget *fontselectiondialog_button_ok;
  GtkWidget *fontselectiondialog_button_cancel;
  GtkWidget *fontselectiondialog_button_apply;
  GtkWidget *font_selection1;

  fontselectiondialog = gtk_font_selection_dialog_new (_("Select Font"));
  gtk_container_set_border_width (GTK_CONTAINER (fontselectiondialog), 4);
  gtk_window_set_position (GTK_WINDOW (fontselectiondialog),
                           GTK_WIN_POS_CENTER);
  gtk_window_set_modal (GTK_WINDOW (fontselectiondialog), TRUE);
  gtk_window_set_type_hint (GTK_WINDOW (fontselectiondialog),
                            GDK_WINDOW_TYPE_HINT_DIALOG);

  fontselectiondialog_button_ok =
    GTK_FONT_SELECTION_DIALOG (fontselectiondialog)->ok_button;
  gtk_widget_show (fontselectiondialog_button_ok);
  GTK_WIDGET_SET_FLAGS (fontselectiondialog_button_ok, GTK_CAN_DEFAULT);

  fontselectiondialog_button_cancel =
    GTK_FONT_SELECTION_DIALOG (fontselectiondialog)->cancel_button;
  gtk_widget_show (fontselectiondialog_button_cancel);
  GTK_WIDGET_SET_FLAGS (fontselectiondialog_button_cancel, GTK_CAN_DEFAULT);

  fontselectiondialog_button_apply =
    GTK_FONT_SELECTION_DIALOG (fontselectiondialog)->apply_button;
  gtk_widget_show (fontselectiondialog_button_apply);
  GTK_WIDGET_SET_FLAGS (fontselectiondialog_button_apply, GTK_CAN_DEFAULT);

  font_selection1 = GTK_FONT_SELECTION_DIALOG (fontselectiondialog)->fontsel;
  gtk_widget_show (font_selection1);
  gtk_container_set_border_width (GTK_CONTAINER (font_selection1), 4);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (fontselectiondialog, fontselectiondialog,
                              "fontselectiondialog");
  GLADE_HOOKUP_OBJECT_NO_REF (fontselectiondialog,
                              fontselectiondialog_button_ok,
                              "fontselectiondialog_button_ok");
  GLADE_HOOKUP_OBJECT_NO_REF (fontselectiondialog,
                              fontselectiondialog_button_cancel,
                              "fontselectiondialog_button_cancel");
  GLADE_HOOKUP_OBJECT_NO_REF (fontselectiondialog,
                              fontselectiondialog_button_apply,
                              "fontselectiondialog_button_apply");
  GLADE_HOOKUP_OBJECT_NO_REF (fontselectiondialog, font_selection1,
                              "font_selection1");

  return fontselectiondialog;
}

GtkWidget *
create_quitdialog (void)
{
  GtkWidget *quitdialog;
  GtkWidget *dialog_vbox4;
  GtkWidget *label2;
  GtkWidget *dialog_action_area4;
  GtkWidget *quitdialog_button_cancel;
  GtkWidget *quitdialog_button_quit;

  quitdialog = gtk_dialog_new ();
  gtk_window_set_title (GTK_WINDOW (quitdialog), _("Quit"));
  gtk_window_set_position (GTK_WINDOW (quitdialog), GTK_WIN_POS_CENTER);
  gtk_window_set_modal (GTK_WINDOW (quitdialog), TRUE);
  gtk_window_set_default_size (GTK_WINDOW (quitdialog), 194, 100);
  gtk_window_set_type_hint (GTK_WINDOW (quitdialog),
                            GDK_WINDOW_TYPE_HINT_DIALOG);

  dialog_vbox4 = GTK_DIALOG (quitdialog)->vbox;
  gtk_widget_show (dialog_vbox4);

  label2 = gtk_label_new (_("Are you sure you want to quit?"));
  gtk_widget_show (label2);
  gtk_box_pack_start (GTK_BOX (dialog_vbox4), label2, TRUE, FALSE, 0);

  dialog_action_area4 = GTK_DIALOG (quitdialog)->action_area;
  gtk_widget_show (dialog_action_area4);
  gtk_button_box_set_layout (GTK_BUTTON_BOX (dialog_action_area4),
                             GTK_BUTTONBOX_END);

  quitdialog_button_cancel = gtk_button_new_from_stock ("gtk-cancel");
  gtk_widget_show (quitdialog_button_cancel);
  gtk_dialog_add_action_widget (GTK_DIALOG (quitdialog),
                                quitdialog_button_cancel,
                                GTK_RESPONSE_CANCEL);
  GTK_WIDGET_SET_FLAGS (quitdialog_button_cancel, GTK_CAN_DEFAULT);

  quitdialog_button_quit = gtk_button_new_from_stock ("gtk-quit");
  gtk_widget_show (quitdialog_button_quit);
  gtk_dialog_add_action_widget (GTK_DIALOG (quitdialog),
                                quitdialog_button_quit, GTK_RESPONSE_OK);
  GTK_WIDGET_SET_FLAGS (quitdialog_button_quit, GTK_CAN_DEFAULT);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (quitdialog, quitdialog, "quitdialog");
  GLADE_HOOKUP_OBJECT_NO_REF (quitdialog, dialog_vbox4, "dialog_vbox4");
  GLADE_HOOKUP_OBJECT (quitdialog, label2, "label2");
  GLADE_HOOKUP_OBJECT_NO_REF (quitdialog, dialog_action_area4,
                              "dialog_action_area4");
  GLADE_HOOKUP_OBJECT (quitdialog, quitdialog_button_cancel,
                       "quitdialog_button_cancel");
  GLADE_HOOKUP_OBJECT (quitdialog, quitdialog_button_quit,
                       "quitdialog_button_quit");

  return quitdialog;
}

GtkWidget *
create_gotodialog (void)
{
  GtkWidget *gotodialog;
  GtkWidget *dialog_vbox5;
  GtkWidget *vbox9;
  GtkWidget *gotodialog_entry;
  GtkWidget *gotodialog_label;
  GtkWidget *dialog_action_area5;
  GtkWidget *gotodialog_button_cancel;
  GtkWidget *gotodialog_button_ok;

  gotodialog = gtk_dialog_new ();
  gtk_window_set_title (GTK_WINDOW (gotodialog), _("Go To Line"));
  gtk_window_set_modal (GTK_WINDOW (gotodialog), TRUE);
  gtk_window_set_default_size (GTK_WINDOW (gotodialog), 194, 100);
  gtk_window_set_type_hint (GTK_WINDOW (gotodialog),
                            GDK_WINDOW_TYPE_HINT_DIALOG);

  dialog_vbox5 = GTK_DIALOG (gotodialog)->vbox;
  gtk_widget_show (dialog_vbox5);

  vbox9 = gtk_vbox_new (FALSE, 0);
  gtk_widget_show (vbox9);
  gtk_box_pack_start (GTK_BOX (dialog_vbox5), vbox9, TRUE, TRUE, 0);

  gotodialog_entry = gtk_entry_new ();
  gtk_widget_show (gotodialog_entry);
  gtk_box_pack_start (GTK_BOX (vbox9), gotodialog_entry, FALSE, FALSE, 0);

  gotodialog_label = gtk_label_new ("");
  gtk_widget_show (gotodialog_label);
  gtk_box_pack_start (GTK_BOX (vbox9), gotodialog_label, FALSE, FALSE, 12);

  dialog_action_area5 = GTK_DIALOG (gotodialog)->action_area;
  gtk_widget_show (dialog_action_area5);
  gtk_button_box_set_layout (GTK_BUTTON_BOX (dialog_action_area5),
                             GTK_BUTTONBOX_END);

  gotodialog_button_cancel = gtk_button_new_from_stock ("gtk-cancel");
  gtk_widget_show (gotodialog_button_cancel);
  gtk_dialog_add_action_widget (GTK_DIALOG (gotodialog),
                                gotodialog_button_cancel,
                                GTK_RESPONSE_CANCEL);
  GTK_WIDGET_SET_FLAGS (gotodialog_button_cancel, GTK_CAN_DEFAULT);

  gotodialog_button_ok = gtk_button_new_from_stock ("gtk-ok");
  gtk_widget_show (gotodialog_button_ok);
  gtk_dialog_add_action_widget (GTK_DIALOG (gotodialog), gotodialog_button_ok,
                                GTK_RESPONSE_OK);
  GTK_WIDGET_SET_FLAGS (gotodialog_button_ok, GTK_CAN_DEFAULT);

  /* Store pointers to all widgets, for use by lookup_widget(). */
  GLADE_HOOKUP_OBJECT_NO_REF (gotodialog, gotodialog, "gotodialog");
  GLADE_HOOKUP_OBJECT_NO_REF (gotodialog, dialog_vbox5, "dialog_vbox5");
  GLADE_HOOKUP_OBJECT (gotodialog, vbox9, "vbox9");
  GLADE_HOOKUP_OBJECT (gotodialog, gotodialog_entry, "gotodialog_entry");
  GLADE_HOOKUP_OBJECT (gotodialog, gotodialog_label, "gotodialog_label");
  GLADE_HOOKUP_OBJECT_NO_REF (gotodialog, dialog_action_area5,
                              "dialog_action_area5");
  GLADE_HOOKUP_OBJECT (gotodialog, gotodialog_button_cancel,
                       "gotodialog_button_cancel");
  GLADE_HOOKUP_OBJECT (gotodialog, gotodialog_button_ok,
                       "gotodialog_button_ok");

  return gotodialog;
}
