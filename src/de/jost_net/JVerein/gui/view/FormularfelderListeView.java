/**********************************************************************
 * $Source$
 * $Revision$
 * $Date$
 * $Author$
 *
 * Copyright (c) by Heiner Jostkleigrewe
 * All rights reserved
 * heiner@jverein.de
 * www.jverein.de
 * $Log$
 * Revision 1.1  2008/07/18 20:12:44  jost
 * Neu: Formulare
 *
 **********************************************************************/
package de.jost_net.JVerein.gui.view;

import de.jost_net.JVerein.gui.action.DokumentationAction;
import de.jost_net.JVerein.gui.action.FormularfeldAction;
import de.jost_net.JVerein.gui.control.FormularfeldControl;
import de.jost_net.JVerein.rmi.Formular;
import de.willuhn.jameica.gui.AbstractView;
import de.willuhn.jameica.gui.GUI;
import de.willuhn.jameica.gui.internal.buttons.Back;
import de.willuhn.jameica.gui.util.ButtonArea;
import de.willuhn.util.ApplicationException;

public class FormularfelderListeView extends AbstractView
{
  public void bind() throws Exception
  {
    GUI.getView().setTitle("Formularfelder");

    FormularfeldControl control = new FormularfeldControl(this,
        (Formular) getCurrentObject());
    control.getFormularfeldList().paint(this.getParent());

    ButtonArea buttons = new ButtonArea(this.getParent(), 3);
    buttons.addButton(new Back(false));
    buttons.addButton("Hilfe", new DokumentationAction(),
        DokumentationUtil.FORMULARE);
    buttons.addButton("neu", new FormularfeldAction(),
        (Formular) getCurrentObject());
  }

  public void unbind() throws ApplicationException
  {
  }
}
